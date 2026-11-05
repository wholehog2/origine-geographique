# -*- coding: utf-8 -*-
"""
Diagramme de type Sankey des origines géographiques des ancêtres,
généré à partir d'un fichier GEDCOM, avec interface graphique.

Fonctionnement
--------------
1. On choisit un fichier GEDCOM (.ged) puis l'individu de départ (G1).
2. Le programme remonte l'arbre (père / mère) sur N générations.
3. Pour chaque génération, les ancêtres sont regroupés par lieu de
   naissance (niveau de lieu réglable : commune, département, pays...).
4. Chaque lien "G(n) : lieu de l'enfant -> G(n+1) : lieu du parent"
   représente le nombre d'ancêtres concernés ; le diagramme est
   écrit en HTML (interactif) et, en option, en JPEG et en CSV.

Dépendances (à installer une fois) :
    pip install plotly numpy
    pip install -U kaleido      # uniquement pour l'export JPEG

Tkinter est fourni avec Python (sous Linux : paquet "python3-tk").
"""

import math
import os
import re
import sys
import colorsys
import queue
import threading
import traceback
import webbrowser
from collections import Counter, defaultdict

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, font as tkfont


# ============================================================
# 1. LECTURE DU FICHIER GEDCOM
# ============================================================

LIGNE_GEDCOM = re.compile(r"^\s*(\d+)\s+(?:(@[^@]+@)\s+)?(\S+)(?:\s(.*))?$")


def reparer_mojibake(texte):
    """Répare les séquences UTF-8 interprétées à tort comme ANSI/Latin-1.

    La réparation est faite caractère par caractère. Ainsi, un caractère
    isolé non représentable en Latin-1 ne bloque pas la correction du reste
    de la ligne ou du fichier.
    """
    marqueurs = ("Ã", "Â", "â", "ð")

    def octet_de(c):
        # Windows-1252 couvre aussi les caractères de ponctuation typiques
        # des fichiers Heredis. Les contrôles Latin-1 restent acceptés.
        try:
            b = c.encode("cp1252")
            if len(b) == 1:
                return b[0]
        except UnicodeEncodeError:
            pass
        try:
            b = c.encode("latin-1")
            if len(b) == 1:
                return b[0]
        except UnicodeEncodeError:
            pass
        return None

    def une_passe(source):
        resultat = []
        i = 0
        while i < len(source):
            c = source[i]
            if c not in marqueurs:
                resultat.append(c)
                i += 1
                continue

            # Reconstitue les octets d'une séquence UTF-8 mojibake (2 à 4
            # octets), sans exiger que toute la chaîne soit en Latin-1.
            octets = []
            j = i
            while j < len(source) and len(octets) < 4:
                b = octet_de(source[j])
                if b is None:
                    break
                octets.append(b)
                j += 1

            corrige = None
            longueur = 0
            for n in (4, 3, 2):
                if len(octets) < n:
                    continue
                bloc = bytes(octets[:n])
                try:
                    candidat = bloc.decode("utf-8")
                except UnicodeDecodeError:
                    continue
                if len(candidat) == 1 and candidat != "\ufffd":
                    corrige = candidat
                    longueur = n
                    break

            if corrige is not None:
                resultat.append(corrige)
                i += longueur
            else:
                resultat.append(c)
                i += 1
        return "".join(resultat)

    # Plusieurs passes couvrent aussi les doubles conversions éventuelles.
    for _ in range(3):
        corrige = une_passe(texte)
        if corrige == texte:
            break
        texte = corrige
    return texte


def decoder_gedcom(chemin):
    """Lit le GEDCOM puis répare les séquences UTF-8 déjà mal décodées."""
    with open(chemin, "rb") as f:
        brut = f.read()

    if brut.startswith(b"\xef\xbb\xbf"):
        texte = brut.decode("utf-8-sig")
    elif brut.startswith((b"\xff\xfe", b"\xfe\xff")):
        texte = brut.decode("utf-16")
    else:
        # Le fichier fourni annonce CHAR UTF-8 : respecter cette déclaration.
        entete = brut[:8000].decode("latin-1", errors="replace").upper()
        m = re.search(r"^\s*1\s+CHAR\s+([^\r\n]+)", entete, re.MULTILINE)
        jeu = m.group(1).strip() if m else ""

        if jeu.startswith(("UTF-8", "UTF8")):
            try:
                texte = brut.decode("utf-8")
            except UnicodeDecodeError:
                texte = brut.decode("cp1252", errors="replace")
        elif jeu.startswith("ANSEL"):
            # ANSEL est un encodage GEDCOM distinct ; traitement dédié
            # à ajouter si un fichier déclare réellement CHAR ANSEL.
            texte = brut.decode("latin-1", errors="replace")
        elif jeu.startswith(("ANSI", "WINDOWS", "CP1252")):
            try:
                texte = brut.decode("utf-8")
            except UnicodeDecodeError:
                texte = brut.decode("cp1252", errors="replace")
        elif jeu.startswith("ISO"):
            texte = brut.decode("latin-1", errors="replace")
        else:
            try:
                texte = brut.decode("utf-8")
            except UnicodeDecodeError:
                texte = brut.decode("cp1252", errors="replace")

    return reparer_mojibake(texte)


def nettoyer_nom(nom):
    """'Jean /DUPONT/' -> 'DUPONT Jean'."""
    if not nom:
        return "(sans nom)"
    m = re.match(r"^(.*?)/(.*?)/(.*)$", nom)
    if m:
        prenom = (m.group(1) + " " + m.group(3)).strip()
        patro = m.group(2).strip()
        resultat = f"{patro} {prenom}".strip()
    else:
        resultat = nom.strip()
    return re.sub(r"\s+", " ", resultat) or "(sans nom)"


def extraire_annee(date):
    if not date:
        return ""
    m = re.search(r"(\d{4})", date)
    return m.group(1) if m else ""


def lire_gedcom(chemin):
    """Retourne (individus, familles).

    individus : xref -> dict(nom, lieu_naissance, lieu_bapteme,
                             annee, famc=[xref de familles])
    familles  : xref -> dict(pere, mere)
    """
    texte = decoder_gedcom(chemin)

    individus = {}
    familles = {}

    courant = None        # enregistrement de niveau 0 en cours
    type_courant = None   # "INDI", "FAM" ou None
    tag1 = None           # dernière balise de niveau 1
    pedi_famc = None      # pour rattacher PEDI à la FAMC en cours

    for ligne in texte.splitlines():
        m = LIGNE_GEDCOM.match(ligne)
        if not m:
            continue
        niveau = int(m.group(1))
        xref = m.group(2)
        tag = m.group(3).upper()
        valeur = (m.group(4) or "").strip()

        if niveau == 0:
            tag1 = None
            pedi_famc = None
            if tag == "INDI" and xref:
                courant = dict(
                    nom="", lieu_naissance="", lieu_bapteme="",
                    annee="", famc=[],
                )
                individus[xref] = courant
                type_courant = "INDI"
            elif tag == "FAM" and xref:
                courant = dict(pere=None, mere=None)
                familles[xref] = courant
                type_courant = "FAM"
            else:
                courant, type_courant = None, None
            continue

        if courant is None:
            continue

        if niveau == 1:
            tag1 = tag
            pedi_famc = None
            if type_courant == "INDI":
                if tag == "NAME" and not courant["nom"]:
                    courant["nom"] = nettoyer_nom(valeur)
                elif tag == "FAMC":
                    pedi_famc = dict(xref=valeur, ok=True)
                    courant["famc"].append(pedi_famc)
            elif type_courant == "FAM":
                if tag == "HUSB":
                    courant["pere"] = valeur
                elif tag == "WIFE":
                    courant["mere"] = valeur
        elif niveau == 2:
            if type_courant == "INDI":
                if tag1 == "BIRT":
                    if tag == "PLAC" and not courant["lieu_naissance"]:
                        courant["lieu_naissance"] = valeur
                    elif tag == "DATE" and not courant["annee"]:
                        courant["annee"] = extraire_annee(valeur)
                elif tag1 in ("CHR", "BAPM"):
                    if tag == "PLAC" and not courant["lieu_bapteme"]:
                        courant["lieu_bapteme"] = valeur
                    elif tag == "DATE" and not courant["annee"]:
                        courant["annee"] = extraire_annee(valeur)
                elif tag1 == "FAMC" and tag == "PEDI" and pedi_famc:
                    # Filiation adoptive / d'accueil : ignorée
                    if valeur.lower() in ("adopted", "foster", "sealing"):
                        pedi_famc["ok"] = False

    for indi in individus.values():
        indi["famc"] = [f["xref"] for f in indi["famc"] if f["ok"]]

    return individus, familles


def parents_de(xref, individus, familles):
    """Liste des parents connus (père, mère) d'un individu."""
    indi = individus.get(xref)
    if not indi:
        return []
    for fam_xref in indi["famc"]:
        fam = familles.get(fam_xref)
        if not fam:
            continue
        parents = [
            p for p in (fam["pere"], fam["mere"]) if p and p in individus
        ]
        if parents:
            return parents
    return []


# ============================================================
# 2. LIEUX
# ============================================================

LIEU_INCONNU = "Lieu inconnu"


def extraire_lieu(brut, niveau, depuis_la_fin):
    """Extrait le composant de lieu voulu dans 'Ville, CP, Dept, Pays'.

    niveau : 1 = premier composant (en partant de la fin ou du début).
    Si le lieu a moins de composants, on prend le plus proche.
    """
    if not brut or not brut.strip():
        return LIEU_INCONNU
    parts = [p.strip() for p in brut.split(",") if p.strip()]
    if not parts:
        return LIEU_INCONNU
    niveau = max(1, niveau)
    if depuis_la_fin:
        i = max(len(parts) - niveau, 0)
    else:
        i = min(niveau - 1, len(parts) - 1)
    return parts[i]


# ============================================================
# 3. CONSTRUCTION DES LIENS (ANCÊTRES -> TABLE SOURCE/CIBLE/VALEUR)
# ============================================================

def construire_liens(individus, familles, racine, nb_generations,
                     niveau_lieu, depuis_la_fin, utiliser_bapteme):
    """Remonte l'ascendance de 'racine' sur 'nb_generations' générations.

    Retourne une liste de dicts :
      gen_source, lieu_source, gen_cible, lieu_cible, valeur
    où valeur = nombre d'ancêtres (emplacements, doublons d'implexe
    inclus) de la génération cible dont le parent est dans cette case.
    """
    # Regroupement insensible à la casse ("calvados" / "Calvados").
    formes = defaultdict(Counter)

    def lieu_brut(xref):
        indi = individus[xref]
        brut = indi["lieu_naissance"]
        if not brut and utiliser_bapteme:
            brut = indi["lieu_bapteme"]
        return extraire_lieu(brut, niveau_lieu, depuis_la_fin)

    lieux_indi = {}

    def lieu_de(xref):
        if xref not in lieux_indi:
            l = lieu_brut(xref)
            formes[l.casefold()][l] += 1
            lieux_indi[xref] = l.casefold()
        return lieux_indi[xref]

    liens = Counter()
    courant = Counter({racine: 1})

    for gen in range(1, nb_generations):
        suivant = Counter()
        for xref, nb in courant.items():
            cle_enfant = (gen, lieu_de(xref))
            for p in parents_de(xref, individus, familles):
                suivant[p] += nb
                liens[(cle_enfant, (gen + 1, lieu_de(p)))] += nb
        if not suivant:
            break
        courant = suivant

    def affichage(cle_lieu):
        return formes[cle_lieu].most_common(1)[0][0]

    resultat = []
    for ((gs, ls), (gc, lc)), v in sorted(liens.items()):
        resultat.append(dict(
            gen_source=gs, lieu_source=affichage(ls),
            gen_cible=gc, lieu_cible=affichage(lc), valeur=v,
        ))
    return resultat


# ============================================================
# 4. DIAGRAMME (PLOTLY)
# ============================================================

def couleur_avec_transparence(couleur, alpha=0.45):
    if couleur.startswith("rgb("):
        v = couleur.replace("rgb(", "").replace(")", "").split(",")
        r, g, b = int(v[0]), int(v[1]), int(v[2])
        return f"rgba({r}, {g}, {b}, {alpha})"
    if couleur.startswith("#"):
        h = couleur.lstrip("#")
        r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
        return f"rgba({r}, {g}, {b}, {alpha})"
    return couleur


def points_courbe_bezier(np, x0, y0, x1, y1, n=24):
    """Courbe en S, tangente horizontale aux deux extrémités."""
    x_milieu = (x0 + x1) / 2
    t = np.linspace(0, 1, n)
    x = (
        (1 - t) ** 3 * x0
        + 3 * (1 - t) ** 2 * t * x_milieu
        + 3 * (1 - t) * t ** 2 * x_milieu
        + t ** 3 * x1
    )
    y = (
        (1 - t) ** 3 * y0
        + 3 * (1 - t) ** 2 * t * y0
        + 3 * (1 - t) * t ** 2 * y1
        + t ** 3 * y1
    )
    return x, y


def construire_figure(liens, p):
    """Construit la figure Plotly. 'p' = dict des paramètres."""
    import numpy as np
    import plotly.graph_objects as go
    from plotly.colors import qualitative

    PIXELS_PAR_UNITE = p["pixels_par_unite"]
    PAD = p["pad_noeuds"]
    LARGEUR_NOEUD = p["largeur_noeud"]
    ESPACE_COL = p["espace_colonnes"]
    MARGE_HAUT, MARGE_BAS = 110, 60
    MARGE_GAUCHE, MARGE_DROITE = 40, 160
    EXPOSANT = math.log(p["facteur_doublement"]) / math.log(2)

    # --- Totaux bruts --------------------------------------------------
    raw_out, raw_in = defaultdict(float), defaultdict(float)
    for l in liens:
        raw_out[(l["gen_source"], l["lieu_source"])] += l["valeur"]
        raw_in[(l["gen_cible"], l["lieu_cible"])] += l["valeur"]

    cles = sorted(set(raw_out) | set(raw_in))
    generations = sorted({c[0] for c in cles})
    gen_min = generations[0]

    # --- Effectif réel et hauteur atténuée -----------------------------
    effectif = {}
    for c in cles:
        if c[0] == gen_min:
            effectif[c] = 1  # G1 = l'individu de départ
        else:
            effectif[c] = raw_in.get(c, raw_out.get(c, 0))

    total_gen = {
        g: sum(effectif[c] for c in cles if c[0] == g) for g in generations
    }
    hauteur = {}
    for c in cles:
        tg = total_gen[c[0]]
        h_tot = tg ** EXPOSANT if tg > 0 else 0
        hauteur[c] = h_tot * (effectif[c] / tg if tg > 0 else 0)

    noeuds_gen = {}
    for g in generations:
        lst = [c for c in cles if c[0] == g]
        lst.sort(key=lambda c: (-hauteur[c], c[1]))
        noeuds_gen[g] = lst

    # --- Couleurs ------------------------------------------------------
    lieux = sorted({c[1] for c in cles})
    palette = (qualitative.Plotly + qualitative.Set2
               + qualitative.Dark24 + qualitative.Light24)

    def couleur_sup(i, total):
        h = (i / max(total, 1)) % 1
        r, g, b = colorsys.hsv_to_rgb(h, 0.65, 0.80)
        return f"rgb({int(r*255)}, {int(g*255)}, {int(b*255)})"

    couleurs = {}
    for i, lieu in enumerate(lieux):
        couleurs[lieu] = (palette[i] if i < len(palette) else
                          couleur_sup(i - len(palette),
                                      len(lieux) - len(palette)))

    # --- Positions -----------------------------------------------------
    haut_col = {}
    for g, lst in noeuds_gen.items():
        haut_col[g] = (sum(hauteur[c] for c in lst) * PIXELS_PAR_UNITE
                       + max(len(lst) - 1, 0) * PAD)
    haut_max = max(haut_col.values())
    HAUTEUR_FIG = MARGE_HAUT + haut_max + MARGE_BAS

    pos = {}
    for i, g in enumerate(generations):
        xg = MARGE_GAUCHE + i * ESPACE_COL
        y = MARGE_HAUT + (haut_max - haut_col[g]) / 2
        for c in noeuds_gen[g]:
            h = hauteur[c] * PIXELS_PAR_UNITE
            pos[c] = dict(xg=xg, xd=xg + LARGEUR_NOEUD, yh=y, yb=y + h)
            y += h + PAD

    # --- Créneaux des liens sur chaque case ----------------------------
    for idx, l in enumerate(liens):
        l["_idx"] = idx
        l["_cs"] = (l["gen_source"], l["lieu_source"])
        l["_cc"] = (l["gen_cible"], l["lieu_cible"])

    depart, arrivee = {}, {}
    for c in cles:
        sortants = sorted((l for l in liens if l["_cs"] == c),
                          key=lambda l: pos[l["_cc"]]["yh"])
        y = pos[c]["yh"]
        hc = pos[c]["yb"] - pos[c]["yh"]
        for l in sortants:
            h = l["valeur"] / raw_out[c] * hc if raw_out[c] > 0 else 0
            depart[l["_idx"]] = (y, y + h)
            y += h

        entrants = sorted((l for l in liens if l["_cc"] == c),
                          key=lambda l: pos[l["_cs"]]["yh"])
        y = pos[c]["yh"]
        for l in entrants:
            h = l["valeur"] / raw_in[c] * hc if raw_in[c] > 0 else 0
            arrivee[l["_idx"]] = (y, y + h)
            y += h

    # --- Rubans --------------------------------------------------------
    fig = go.Figure()
    for l in liens:
        xd = pos[l["_cs"]]["xd"]
        xa = pos[l["_cc"]]["xg"]
        y0h, y0b = depart[l["_idx"]]
        y1h, y1b = arrivee[l["_idx"]]
        xh, yh = points_courbe_bezier(np, xd, y0h, xa, y1h)
        xb, yb = points_courbe_bezier(np, xd, y0b, xa, y1b)
        fig.add_trace(go.Scatter(
            x=np.concatenate([xh, xb[::-1]]),
            y=np.concatenate([yh, yb[::-1]]),
            mode="lines", line=dict(width=0), fill="toself",
            fillcolor=couleur_avec_transparence(
                couleurs[l["lieu_source"]], 0.45),
            hoveron="fills", hoverinfo="text",
            text=(f"<b>{l['lieu_source']}</b> → <b>{l['lieu_cible']}</b>"
                  f"<br>Génération {l['gen_source']} → "
                  f"Génération {l['gen_cible']}"
                  f"<br>Nombre d'individus : <b>{l['valeur']:g}</b>"),
            showlegend=False,
        ))

    # --- Cases et étiquettes -------------------------------------------
    annotations = []
    for c in cles:
        g, lieu = c
        q = pos[c]
        fig.add_trace(go.Scatter(
            x=[q["xg"], q["xd"], q["xd"], q["xg"], q["xg"]],
            y=[q["yh"], q["yh"], q["yb"], q["yb"], q["yh"]],
            mode="lines", line=dict(color="rgba(80,80,80,0.6)", width=0.5),
            fill="toself", fillcolor=couleurs[lieu],
            hoveron="fills", hoverinfo="text",
            text=(f"<b>{lieu}</b><br>Génération {g}"
                  f"<br>Effectif : <b>{effectif[c]:g}</b>"),
            showlegend=False,
        ))
        annotations.append(dict(
            x=q["xd"] + 8, y=(q["yh"] + q["yb"]) / 2, xref="x", yref="y",
            text=lieu, showarrow=False, xanchor="left", yanchor="middle",
            font=dict(size=13, color="#333"),
            bgcolor="rgba(255,255,255,0.75)",
        ))

    for g in generations:
        c0 = noeuds_gen[g][0]
        annotations.append(dict(
            x=(pos[c0]["xg"] + pos[c0]["xd"]) / 2, y=-18,
            xref="x", yref="y",
            text=(f"<b>Génération {g}</b>"
                  f"<br><span style='font-size:12px'>"
                  f"Total : {total_gen[g]:g}</span>"),
            showarrow=False, xanchor="center", yanchor="bottom",
            align="center", font=dict(size=15),
        ))

    largeur_fig = (MARGE_GAUCHE + (len(generations) - 1) * ESPACE_COL
                   + LARGEUR_NOEUD + MARGE_DROITE)

    fig.update_layout(
        title=dict(text=p["titre"], x=0.5, xanchor="center",
                   font=dict(size=20)),
        annotations=annotations,
        font=dict(family="Arial", size=12),
        width=largeur_fig, height=HAUTEUR_FIG,
        margin=dict(l=10, r=10, t=90, b=10),
        paper_bgcolor="white", plot_bgcolor="white",
        xaxis=dict(visible=False, range=[0, largeur_fig], fixedrange=True),
        yaxis=dict(visible=False,
                   range=[HAUTEUR_FIG - MARGE_BAS, -30], fixedrange=True),
        hoverlabel=dict(bgcolor="white", font_size=13),
    )
    return fig


def exporter_csv(liens, chemin):
    """Même format que l'ancien fichier Excel (Source / Cible / Valeur)."""
    import csv
    with open(chemin, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["Source (Génération N)", "Cible (Génération N+1)",
                    "Valeur (Nb d'individus)"])
        for l in liens:
            w.writerow([f"G{l['gen_source']} : {l['lieu_source']}",
                        f"G{l['gen_cible']} : {l['lieu_cible']}",
                        f"{l['valeur']:g}"])


# ============================================================
# 5. TRAITEMENT COMPLET (utilisé par l'interface)
# ============================================================

def generer(p, log):
    """Pipeline complet. Retourne le chemin du HTML créé."""
    individus, familles = lire_gedcom(p["gedcom"])
    log(f"GEDCOM relu : {len(individus)} individus, "
        f"{len(familles)} familles.")

    liens = construire_liens(
        individus, familles, p["racine"], p["nb_generations"],
        p["niveau_lieu"], p["depuis_la_fin"], p["utiliser_bapteme"],
    )
    if not liens:
        raise ValueError(
            "Aucun ancêtre trouvé pour cet individu : il n'a pas de "
            "parents rattachés dans le fichier GEDCOM."
        )
    gens = sorted({l["gen_cible"] for l in liens})
    log(f"Générations atteintes : G1 à G{gens[-1]} "
        f"({len(liens)} liens).")

    if p["csv"]:
        exporter_csv(liens, p["csv"])
        log(f"Données CSV créées : {p['csv']}")

    fig = construire_figure(liens, p)

    fig.write_html(p["html"], include_plotlyjs=True, full_html=True)
    log(f"Diagramme créé : {p['html']}")

    if p["jpeg"]:
        try:
            fig.write_image(p["jpeg"], format="jpeg",
                            scale=p["resolution_jpeg"])
            log(f"Image JPEG créée : {p['jpeg']}")
        except Exception as e:
            log("Échec de l'export JPEG : "
                f"{e}\n -> Vérifiez que 'kaleido' est installé "
                "(pip install -U kaleido).")
    return p["html"]


# ============================================================
# 6. INTERFACE GRAPHIQUE
# ============================================================

class Application(ttk.Frame):

    def __init__(self, master):
        super().__init__(master, padding=10)
        self.master = master
        master.title("Origines géographiques · Analyse GEDCOM")
        master.configure(bg="#eef2f7")
        master.option_add("*Font", ("DejaVu Sans", 10))
        self._configurer_style()
        self.pack(fill="both", expand=True)

        # Zone de contenu défilante : tous les réglages restent accessibles,
        # même lorsque la hauteur de l'écran est inférieure à celle de l'UI.
        self.canvas = tk.Canvas(self, highlightthickness=0, bd=0,
                                background="#eef2f7")
        self.scrollbar = ttk.Scrollbar(self, orient="vertical",
                                       command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.scrollbar.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.contenu = ttk.Frame(self.canvas)
        self._fenetre_contenu = self.canvas.create_window(
            (0, 0), window=self.contenu, anchor="nw")
        self.contenu.bind("<Configure>", self._maj_zone_defilante)
        self.canvas.bind("<Configure>", self._adapter_largeur_contenu)
        self.canvas.bind_all("<MouseWheel>", self._defiler_souris)
        self.canvas.bind_all("<Button-4>", lambda e: self.canvas.yview_scroll(-3, "units"))
        self.canvas.bind_all("<Button-5>", lambda e: self.canvas.yview_scroll(3, "units"))

        self.individus = {}
        self.familles = {}
        self.liste_affichee = []   # xref des individus visibles
        self.file_logs = queue.Queue()

        # Variables
        self.v_gedcom = tk.StringVar()
        self.v_recherche = tk.StringVar()
        self.v_nb_gen = tk.IntVar(value=8)
        self.v_niveau = tk.IntVar(value=3)
        self.v_sens = tk.StringVar(value="fin")
        self.v_bapteme = tk.BooleanVar(value=True)

        self.v_titre = tk.StringVar(value="Évolution des origines "
                                          "géographiques")
        self.v_px_unite = tk.DoubleVar(value=90)
        self.v_pad = tk.DoubleVar(value=24)
        self.v_facteur = tk.DoubleVar(value=1.25)
        self.v_larg_noeud = tk.DoubleVar(value=22)
        self.v_esp_col = tk.DoubleVar(value=260)

        self.v_html = tk.StringVar()
        self.v_jpeg_on = tk.BooleanVar(value=False)
        self.v_jpeg = tk.StringVar()
        self.v_resolution = tk.DoubleVar(value=2)
        self.v_csv_on = tk.BooleanVar(value=False)
        self.v_ouvrir = tk.BooleanVar(value=True)

        self._construire_ui()
        for v in (self.v_niveau, self.v_sens):
            v.trace_add("write", lambda *a: self._maj_apercu_lieux())
        self.v_recherche.trace_add("write", lambda *a: self._filtrer())
        self.after(150, self._lire_logs)

    def _maj_zone_defilante(self, event=None):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _adapter_largeur_contenu(self, event):
        self.canvas.itemconfigure(self._fenetre_contenu, width=event.width)

    def _defiler_souris(self, event):
        if event.delta:
            self.canvas.yview_scroll(int(-event.delta / 120), "units")

    # ---------- style et construction ----------
    def _configurer_style(self):
        """Thème clair moderne, sans dépendance externe."""
        style = ttk.Style(self.master)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        self.couleurs = {
            "fond": "#eef2f7",
            "carte": "#ffffff",
            "texte": "#172033",
            "secondaire": "#64748b",
            "accent": "#2563eb",
            "accent_survol": "#1d4ed8",
            "bordure": "#dbe3ee",
            "champ": "#f8fafc",
        }
        c = self.couleurs
        style.configure("App.TFrame", background=c["fond"])
        style.configure("Card.TLabelframe", background=c["carte"],
                        bordercolor=c["bordure"], relief="solid", borderwidth=1)
        style.configure("Card.TLabelframe.Label", background=c["carte"],
                        foreground=c["accent"], font=("DejaVu Sans", 10, "bold"))
        style.configure("TLabel", background=c["carte"], foreground=c["texte"])
        style.configure("Muted.TLabel", background=c["carte"],
                        foreground=c["secondaire"], font=("DejaVu Sans", 9))
        style.configure("Title.TLabel", background=c["fond"],
                        foreground=c["texte"], font=("DejaVu Sans", 19, "bold"))
        style.configure("Subtitle.TLabel", background=c["fond"],
                        foreground=c["secondaire"], font=("DejaVu Sans", 10))
        style.configure("TEntry", fieldbackground=c["champ"],
                        foreground=c["texte"], bordercolor=c["bordure"],
                        padding=(8, 7))
        style.configure("TSpinbox", fieldbackground=c["champ"],
                        foreground=c["texte"], bordercolor=c["bordure"],
                        padding=(6, 5), arrowsize=12)
        style.configure("TButton", background="#e8eef8", foreground=c["texte"],
                        bordercolor=c["bordure"], padding=(12, 7),
                        font=("DejaVu Sans", 9, "bold"))
        style.map("TButton", background=[("active", "#dbe7f7")])
        style.configure("Primary.TButton", background=c["accent"],
                        foreground="#ffffff", bordercolor=c["accent"],
                        padding=(14, 11), font=("DejaVu Sans", 10, "bold"))
        style.map("Primary.TButton",
                  background=[("active", c["accent_survol"]),
                              ("disabled", "#94a3b8")],
                  foreground=[("disabled", "#f8fafc")])
        style.configure("TRadiobutton", background=c["carte"],
                        foreground=c["texte"], padding=(3, 5))
        style.configure("TCheckbutton", background=c["carte"],
                        foreground=c["texte"], padding=(3, 5))
        style.configure("Vertical.TScrollbar", background="#e8eef8",
                        troughcolor=c["champ"], bordercolor=c["bordure"],
                        arrowsize=12)

    def _construire_ui(self):
        contenu = self.contenu
        c = self.couleurs
        contenu.configure(style="App.TFrame", padding=(18, 14))
        contenu.columnconfigure(0, weight=1)
        contenu.columnconfigure(1, weight=1)
        contenu.rowconfigure(3, weight=1)
        contenu.rowconfigure(6, weight=1)

        # En-tête
        entete = ttk.Frame(contenu, style="App.TFrame")
        entete.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 14))
        ttk.Label(entete, text="Origines géographiques",
                  style="Title.TLabel").pack(anchor="w")
        ttk.Label(entete,
                  text="Explorez les lieux de naissance de vos ancêtres à partir d’un fichier GEDCOM.",
                  style="Subtitle.TLabel").pack(anchor="w", pady=(3, 0))

        # 1. Source et individu de départ
        f = ttk.LabelFrame(contenu, text="  1  ·  Fichier source et individu de départ  ",
                           style="Card.TLabelframe", padding=12)
        f.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(0, 10))
        f.columnconfigure(1, weight=1)
        ttk.Label(f, text="Fichier GEDCOM").grid(row=0, column=0, sticky="w")
        ttk.Entry(f, textvariable=self.v_gedcom).grid(
            row=0, column=1, sticky="ew", padx=(10, 8))
        ttk.Button(f, text="Parcourir…", command=self._choisir_gedcom).grid(
            row=0, column=2)

        ttk.Label(f, text="Individu de départ (G1)").grid(
            row=1, column=0, sticky="nw", pady=(12, 0))
        zone = ttk.Frame(f)
        zone.grid(row=1, column=1, columnspan=2, sticky="nsew",
                  padx=(10, 0), pady=(10, 0))
        zone.columnconfigure(0, weight=1)
        zone.rowconfigure(1, weight=1)
        recherche = ttk.Frame(zone)
        recherche.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 6))
        recherche.columnconfigure(0, weight=1)
        ttk.Entry(recherche, textvariable=self.v_recherche).grid(
            row=0, column=0, sticky="ew")
        ttk.Label(recherche, text="Filtrer par nom ou identifiant",
                  style="Muted.TLabel").grid(row=0, column=1, padx=(10, 0))
        self.liste = tk.Listbox(
            zone, height=6, exportselection=False, activestyle="none",
            relief="flat", borderwidth=0, highlightthickness=1,
            highlightbackground=c["bordure"], highlightcolor=c["accent"],
            background="#f8fafc", foreground=c["texte"],
            selectbackground="#dbeafe", selectforeground="#1e3a8a",
            font=("DejaVu Sans", 10))
        sb = ttk.Scrollbar(zone, orient="vertical", command=self.liste.yview)
        self.liste.configure(yscrollcommand=sb.set)
        self.liste.grid(row=1, column=0, sticky="nsew")
        sb.grid(row=1, column=1, sticky="ns")
        self.lbl_info = ttk.Label(zone, text="Aucun fichier chargé.",
                                  style="Muted.TLabel")
        self.lbl_info.grid(row=2, column=0, columnspan=2, sticky="w", pady=(5, 0))

        # 2. Paramètres généalogiques
        g = ttk.LabelFrame(contenu, text="  2  ·  Ascendance et lieux  ",
                           style="Card.TLabelframe", padding=12)
        g.grid(row=2, column=0, sticky="nsew", padx=(0, 5), pady=(0, 10))
        g.columnconfigure(1, weight=1)
        ttk.Label(g, text="Nombre de générations (G1 incluse)").grid(
            row=0, column=0, columnspan=2, sticky="w")
        ttk.Spinbox(g, from_=2, to=30, width=7,
                    textvariable=self.v_nb_gen).grid(
            row=1, column=0, sticky="w", pady=(4, 9))
        ttk.Label(g, text="Niveau du lieu à retenir").grid(
            row=2, column=0, columnspan=2, sticky="w")
        ttk.Spinbox(g, from_=1, to=10, width=7,
                    textvariable=self.v_niveau).grid(
            row=3, column=0, sticky="w", pady=(4, 7))
        ttk.Radiobutton(g, text="Compter depuis la fin (pays = 1)",
                        variable=self.v_sens, value="fin").grid(
            row=4, column=0, columnspan=2, sticky="w")
        ttk.Radiobutton(g, text="Compter depuis le début (commune = 1)",
                        variable=self.v_sens, value="debut").grid(
            row=5, column=0, columnspan=2, sticky="w")
        ttk.Checkbutton(g, text="Utiliser le baptême si naissance absente",
                        variable=self.v_bapteme).grid(
            row=6, column=0, columnspan=2, sticky="w", pady=(3, 7))
        ttk.Label(g, text="APERÇU  ·  LIEU RETENU  ←  LIEU GEDCOM",
                  style="Muted.TLabel").grid(
            row=7, column=0, columnspan=2, sticky="w", pady=(5, 5))
        self.apercu = tk.Text(
            g, height=6, width=42, wrap="word", state="disabled",
            background="#f8fafc", foreground=c["texte"],
            relief="flat", borderwidth=0, padx=9, pady=8,
            highlightthickness=1, highlightbackground=c["bordure"],
            font=("DejaVu Sans", 9))
        self.apercu.grid(row=8, column=0, columnspan=2, sticky="nsew")
        g.rowconfigure(8, weight=1)

        # 3. Apparence du diagramme
        a = ttk.LabelFrame(contenu, text="  3  ·  Apparence du diagramme  ",
                           style="Card.TLabelframe", padding=12)
        a.grid(row=2, column=1, sticky="nsew", padx=(5, 0), pady=(0, 10))
        a.columnconfigure(1, weight=1)
        ttk.Label(a, text="Titre du diagramme").grid(row=0, column=0, sticky="w")
        ttk.Entry(a, textvariable=self.v_titre).grid(
            row=0, column=1, sticky="ew", padx=(8, 0))
        champs = [
            ("Pixels par individu", self.v_px_unite, 10, 500, 5),
            ("Écart entre les cases (px)", self.v_pad, 0, 200, 2),
            ("Atténuation (× par doublement)", self.v_facteur, 1.0, 2.0, 0.05),
            ("Largeur d’une case (px)", self.v_larg_noeud, 4, 100, 2),
            ("Distance entre générations (px)", self.v_esp_col, 80, 800, 10),
        ]
        for i, (txt, var, mini, maxi, pas) in enumerate(champs, start=1):
            ttk.Label(a, text=txt).grid(row=i, column=0, sticky="w", pady=(9, 0))
            ttk.Spinbox(a, from_=mini, to=maxi, increment=pas, width=9,
                        textvariable=var).grid(
                row=i, column=1, sticky="w", padx=(8, 0), pady=(9, 0))
        ttk.Label(
            a, foreground=c["secondaire"], wraplength=340, justify="left",
            text="Atténuation : 2,0 = hauteur proportionnelle à l’effectif. "
                 "1,25 = la hauteur augmente de 25 % quand l’effectif double.",
            style="Muted.TLabel"
        ).grid(row=6, column=0, columnspan=2, sticky="w", pady=(13, 0))

        # 4. Export
        e = ttk.LabelFrame(contenu, text="  4  ·  Export des résultats  ",
                           style="Card.TLabelframe", padding=12)
        e.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(0, 10))
        e.columnconfigure(1, weight=1)
        ttk.Label(e, text="Fichier HTML").grid(row=0, column=0, sticky="w")
        ttk.Entry(e, textvariable=self.v_html).grid(
            row=0, column=1, sticky="ew", padx=9)
        ttk.Button(e, text="Choisir…", command=self._choisir_html).grid(row=0, column=2)
        ttk.Checkbutton(e, text="Exporter également en JPEG",
                        variable=self.v_jpeg_on).grid(
            row=1, column=0, sticky="w", pady=(9, 0))
        ttk.Entry(e, textvariable=self.v_jpeg).grid(
            row=1, column=1, sticky="ew", padx=9, pady=(9, 0))
        ttk.Button(e, text="Choisir…", command=self._choisir_jpeg).grid(
            row=1, column=2, pady=(9, 0))
        ttk.Label(e, text="Résolution JPEG (×)").grid(
            row=2, column=0, sticky="w", pady=(9, 0))
        ttk.Spinbox(e, from_=1, to=6, increment=0.5, width=7,
                    textvariable=self.v_resolution).grid(
            row=2, column=1, sticky="w", padx=9, pady=(9, 0))
        opts = ttk.Frame(e)
        opts.grid(row=3, column=0, columnspan=3, sticky="w", pady=(7, 0))
        ttk.Checkbutton(opts, text="Exporter les liens en CSV (Excel)",
                        variable=self.v_csv_on).pack(side="left", padx=(0, 18))
        ttk.Checkbutton(opts, text="Ouvrir le HTML à la fin",
                        variable=self.v_ouvrir).pack(side="left")

        # Lancement et journal
        self.btn = ttk.Button(contenu, text="GÉNÉRER LE DIAGRAMME",
                              style="Primary.TButton", command=self._lancer)
        self.btn.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(1, 10))
        journal_card = ttk.LabelFrame(
            contenu, text="  Journal  ·  Suivi de la génération  ",
            style="Card.TLabelframe", padding=9)
        journal_card.grid(row=5, column=0, columnspan=2, sticky="nsew")
        journal_card.columnconfigure(0, weight=1)
        journal_card.rowconfigure(0, weight=1)
        self.journal = tk.Text(
            journal_card, height=5, state="disabled", wrap="word",
            background="#f8fafc", foreground="#475569", relief="flat",
            borderwidth=0, padx=8, pady=7, font=("DejaVu Sans Mono", 9),
            highlightthickness=1, highlightbackground=c["bordure"])
        self.journal.grid(row=0, column=0, sticky="nsew")
        journal_sb = ttk.Scrollbar(journal_card, orient="vertical",
                                   command=self.journal.yview)
        journal_sb.grid(row=0, column=1, sticky="ns")
        self.journal.configure(yscrollcommand=journal_sb.set)
        contenu.rowconfigure(5, weight=1)

    # ---------- utilitaires ----------
    def log(self, message):
        """Thread-safe : met le message en file d'attente."""
        self.file_logs.put(message)

    def _lire_logs(self):
        try:
            while True:
                msg = self.file_logs.get_nowait()
                if isinstance(msg, tuple):       # commande interne
                    msg[0](*msg[1:])
                else:
                    self._ecrire_journal(msg)
        except queue.Empty:
            pass
        self.after(150, self._lire_logs)

    def _ecrire_journal(self, msg):
        self.journal.configure(state="normal")
        self.journal.insert("end", msg + "\n")
        self.journal.see("end")
        self.journal.configure(state="disabled")

    # ---------- chargement GEDCOM ----------
    def _choisir_gedcom(self):
        chemin = filedialog.askopenfilename(
            title="Choisir un fichier GEDCOM",
            filetypes=[("GEDCOM", "*.ged *.gedcom"),
                       ("Tous les fichiers", "*.*")])
        if not chemin:
            return
        self.v_gedcom.set(chemin)
        base = os.path.splitext(chemin)[0]
        self.v_html.set(base + "_sankey.html")
        self.v_jpeg.set(base + "_sankey.jpg")
        self._charger(chemin)

    def _charger(self, chemin):
        try:
            self.individus, self.familles = lire_gedcom(chemin)
        except Exception as e:
            messagebox.showerror("Lecture impossible", str(e))
            return
        if not self.individus:
            messagebox.showwarning(
                "Fichier vide",
                "Aucun individu trouvé : est-ce bien un fichier GEDCOM ?")
            return

        # Ordre alphabétique ; présélection du premier du fichier.
        self.ordre = sorted(
            self.individus,
            key=lambda x: self.individus[x]["nom"].casefold())
        self.premier = next(iter(self.individus))
        self.lbl_info.configure(
            text=f"{len(self.individus)} individus, "
                 f"{len(self.familles)} familles.")
        self.v_recherche.set("")
        self._filtrer(selection=self.premier)
        self._maj_apercu_lieux()

    def _libelle(self, xref):
        i = self.individus[xref]
        annee = f" ({i['annee']})" if i["annee"] else ""
        return f"{i['nom']}{annee}   {xref}"

    def _filtrer(self, selection=None):
        if not self.individus:
            return
        terme = self.v_recherche.get().strip().casefold()
        garder = selection or (self._xref_selectionne()
                               if self.liste.curselection() else None)
        self.liste.delete(0, "end")
        self.liste_affichee = []
        for x in self.ordre:
            if (not terme or terme in self.individus[x]["nom"].casefold()
                    or terme in x.casefold()):
                self.liste_affichee.append(x)
                self.liste.insert("end", self._libelle(x))
        if self.liste_affichee:
            if garder in self.liste_affichee:
                i = self.liste_affichee.index(garder)
            else:
                i = 0
            self.liste.selection_set(i)
            self.liste.see(i)

    def _xref_selectionne(self):
        sel = self.liste.curselection()
        if not sel:
            return None
        return self.liste_affichee[sel[0]]

    def _maj_apercu_lieux(self):
        """Montre comment quelques lieux du fichier seront découpés."""
        if not self.individus:
            return
        try:
            niveau = int(self.v_niveau.get())
        except (tk.TclError, ValueError):
            return
        vus, lignes = set(), []
        for indi in self.individus.values():
            brut = indi["lieu_naissance"] or indi["lieu_bapteme"]
            if brut and brut not in vus:
                vus.add(brut)
                retenu = extraire_lieu(brut, niveau,
                                       self.v_sens.get() == "fin")
                lignes.append(f"{retenu}  ←  {brut}")
            if len(lignes) >= 12:
                break
        contenu = "\n".join(lignes) or "(aucun lieu)"
        self.apercu.configure(state="normal")
        self.apercu.delete("1.0", "end")
        self.apercu.insert("end", contenu)
        self.apercu.configure(state="disabled")

        # Ajuste automatiquement la taille de la fenêtre pour rendre
        # l'aperçu aussi lisible que possible, sans dépasser l'écran.
        self._ajuster_fenetre_apercu(lignes or ["(aucun lieu)"])

    def _ajuster_fenetre_apercu(self, lignes):
        """Ajuste la largeur si possible ; la hauteur reste défilante."""
        self.update_idletasks()
        ecran_l = self.winfo_screenwidth()
        ecran_h = self.winfo_screenheight()
        police = tkfont.Font(font=self.apercu.cget("font"))
        largeur_texte = max((police.measure(ligne) for ligne in lignes), default=0)
        largeur_voulue = max(1040, largeur_texte * 2 + 820)
        largeur = min(largeur_voulue, max(860, ecran_l - 80))
        hauteur = min(900, max(650, ecran_h - 100))
        self.master.minsize(min(860, largeur), min(600, hauteur))
        self.master.geometry(f"{largeur}x{hauteur}")
        self.update_idletasks()

    # ---------- choix de fichiers de sortie ----------
    def _choisir_html(self):
        c = filedialog.asksaveasfilename(
            defaultextension=".html", initialfile=os.path.basename(
                self.v_html.get() or "diagramme_sankey.html"),
            filetypes=[("HTML", "*.html")])
        if c:
            self.v_html.set(c)

    def _choisir_jpeg(self):
        c = filedialog.asksaveasfilename(
            defaultextension=".jpg", initialfile=os.path.basename(
                self.v_jpeg.get() or "diagramme_sankey.jpg"),
            filetypes=[("JPEG", "*.jpg *.jpeg")])
        if c:
            self.v_jpeg.set(c)

    # ---------- lancement ----------
    def _lire_parametres(self):
        if not self.individus:
            raise ValueError("Choisissez d'abord un fichier GEDCOM.")
        racine = self._xref_selectionne()
        if not racine:
            raise ValueError("Sélectionnez l'individu de départ.")
        if not self.v_html.get().strip():
            raise ValueError("Indiquez un fichier HTML de sortie.")

        try:
            p = dict(
                gedcom=self.v_gedcom.get(),
                racine=racine,
                nb_generations=int(self.v_nb_gen.get()),
                niveau_lieu=int(self.v_niveau.get()),
                depuis_la_fin=self.v_sens.get() == "fin",
                utiliser_bapteme=self.v_bapteme.get(),
                titre=self.v_titre.get(),
                pixels_par_unite=float(self.v_px_unite.get()),
                pad_noeuds=float(self.v_pad.get()),
                facteur_doublement=float(self.v_facteur.get()),
                largeur_noeud=float(self.v_larg_noeud.get()),
                espace_colonnes=float(self.v_esp_col.get()),
                html=self.v_html.get().strip(),
                jpeg=(self.v_jpeg.get().strip()
                      if self.v_jpeg_on.get() else None),
                resolution_jpeg=float(self.v_resolution.get()),
                csv=(os.path.splitext(self.v_html.get().strip())[0]
                     + "_liens.csv") if self.v_csv_on.get() else None,
            )
        except (tk.TclError, ValueError):
            raise ValueError("Un des paramètres numériques est invalide.")

        if p["nb_generations"] < 2:
            raise ValueError("Il faut au moins 2 générations.")
        if p["facteur_doublement"] <= 0:
            raise ValueError("L'atténuation doit être strictement "
                             "positive.")
        if self.v_jpeg_on.get() and not p["jpeg"]:
            raise ValueError("Indiquez un fichier JPEG.")
        return p

    def _lancer(self):
        try:
            p = self._lire_parametres()
        except ValueError as e:
            messagebox.showwarning("Paramètres", str(e))
            return

        self.btn.configure(state="disabled", text="Génération en cours…")
        self.log("─" * 40)
        self.log(f"Individu de départ : "
                 f"{self.individus[p['racine']]['nom']}")

        def travail():
            try:
                chemin = generer(p, self.log)
                self.file_logs.put((self._fin, chemin, None))
            except Exception as e:
                self.log(traceback.format_exc())
                self.file_logs.put((self._fin, None, e))

        threading.Thread(target=travail, daemon=True).start()

    def _fin(self, chemin, erreur):
        self.btn.configure(state="normal", text="Générer le diagramme")
        if erreur is not None:
            messagebox.showerror("Erreur", str(erreur))
            return
        self.log("Terminé.")
        if self.v_ouvrir.get() and chemin:
            webbrowser.open("file://" + os.path.abspath(chemin))


# ============================================================
# 7. POINT D'ENTRÉE
# ============================================================

def verifier_dependances():
    manquants = []
    for nom in ("numpy", "plotly"):
        try:
            __import__(nom)
        except ImportError:
            manquants.append(nom)
    return manquants


def main():
    racine = tk.Tk()
    largeur_ecran = racine.winfo_screenwidth()
    hauteur_ecran = racine.winfo_screenheight()
    racine.geometry(f"{min(1180, largeur_ecran - 80)}x{min(900, hauteur_ecran - 100)}")
    racine.minsize(860, 600)

    manquants = verifier_dependances()
    if manquants:
        messagebox.showerror(
            "Modules manquants",
            "Modules Python à installer :\n\n"
            f"    pip install {' '.join(manquants)}\n\n"
            "(et, pour l'export JPEG : pip install -U kaleido)")
        racine.destroy()
        sys.exit(1)

    Application(racine)
    racine.mainloop()


if __name__ == "__main__":
    main()
