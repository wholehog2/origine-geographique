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
    pip install plotly numpy pillow

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
from tkinter import ttk, filedialog, messagebox


# ============================================================
# 0. VERSION
# ============================================================

# Numéro de version : à changer ici à chaque publication. Il s'affiche
# en haut à droite de la fenêtre, dans son titre, dans le journal, et avec
#     python geo-gedcom.py --version
VERSION = "1.02"


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
    """Retourne (individus, familles, format_lieu).

    individus : xref -> dict(nom, lieu_naissance, lieu_bapteme,
                             annee, famc=[xref de familles])
    familles  : xref -> dict(pere, mere)
    """
    texte = decoder_gedcom(chemin)

    individus = {}
    familles = {}

    format_lieu = None    # ex. ["Town", "Area code", ..., "Country", ...]
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
            elif tag == "HEAD":
                courant, type_courant = dict(), "HEAD"
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
            if type_courant == "HEAD":
                if tag1 == "PLAC" and tag == "FORM" and valeur:
                    format_lieu = [x.strip() for x in valeur.split(",")]
            elif type_courant == "INDI":
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

    return individus, familles, format_lieu


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


NOMS_PAYS = ("country", "pays")


def indice_pays(format_lieu):
    """Position (à partir de 0) du pays d'après la déclaration
    'PLAC / FORM' de l'en-tête du GEDCOM, ou None si absente."""
    for i, nom in enumerate(format_lieu or []):
        if nom.strip().casefold() in NOMS_PAYS:
            return i
    return None


def extraire_pays(parts, index_pays):
    """Pays d'un lieu déjà découpé ('' si non renseigné).

    On utilise la position annoncée par l'en-tête du GEDCOM ; à défaut
    (ou si le lieu est trop court), on prend le dernier élément rempli.
    """
    if index_pays is not None and index_pays < len(parts):
        return parts[index_pays]
    for p in reversed(parts):
        if p:
            return p
    return ""


def extraire_lieu(brut, niveau, depuis_la_fin, ajouter_pays=False,
                  pays_en_premier=False, index_pays=None):
    """Extrait le composant de lieu voulu dans 'Ville, CP, Dept, Pays'.

    Les composants vides sont CONSERVÉS pour ne pas décaler les niveaux :
      "Rio,,Grande Rio,Rio,BRASIL,"  -> 6 composants dont le 2e et le
      dernier sont vides. Une virgule finale signale un dernier élément
      manquant.
    Si le composant demandé est vide, le lieu est "Lieu inconnu".

    niveau : 1 = premier composant (en partant de la fin ou du début).
    Si le lieu a moins de composants, on prend le plus proche.

    ajouter_pays : ajoute le pays au lieu, séparé par un tiret, avant
    (pays_en_premier) ou après. Rien n'est ajouté si le pays est vide
    ou identique au lieu retenu.
    """
    if not brut or not brut.strip():
        return LIEU_INCONNU
    parts = [p.strip() for p in brut.split(",")]
    niveau = max(1, niveau)
    if depuis_la_fin:
        i = max(len(parts) - niveau, 0)
    else:
        i = min(niveau - 1, len(parts) - 1)
    lieu = parts[i] or LIEU_INCONNU

    if ajouter_pays:
        pays = extraire_pays(parts, index_pays)
        if pays and pays.casefold() != lieu.casefold():
            return f"{pays} - {lieu}" if pays_en_premier \
                else f"{lieu} - {pays}"
    return lieu


# ============================================================
# 3. CONSTRUCTION DES LIENS (ANCÊTRES -> TABLE SOURCE/CIBLE/VALEUR)
# ============================================================

def construire_liens(individus, familles, racine, nb_generations,
                     niveau_lieu, depuis_la_fin, utiliser_bapteme,
                     ajouter_pays=False, pays_en_premier=False,
                     index_pays=None):
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
        return extraire_lieu(brut, niveau_lieu, depuis_la_fin,
                             ajouter_pays, pays_en_premier, index_pays)

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


def _rgb(couleur):
    """'rgb(1, 2, 3)' ou '#rrggbb' -> (r, g, b)."""
    if couleur.startswith("rgb"):
        v = couleur[couleur.index("(") + 1:couleur.index(")")].split(",")
        return int(v[0]), int(v[1]), int(v[2])
    h = couleur.lstrip("#")
    return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)


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
    geo = dict(rubans=[], cases=[], textes=[])   # pour l'export Pillow
    for l in liens:
        xd = pos[l["_cs"]]["xd"]
        xa = pos[l["_cc"]]["xg"]
        y0h, y0b = depart[l["_idx"]]
        y1h, y1b = arrivee[l["_idx"]]
        xh, yh = points_courbe_bezier(np, xd, y0h, xa, y1h)
        xb, yb = points_courbe_bezier(np, xd, y0b, xa, y1b)
        geo["rubans"].append((
            np.concatenate([xh, xb[::-1]]),
            np.concatenate([yh, yb[::-1]]),
            _rgb(couleurs[l["lieu_source"]])))
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
        geo["cases"].append((q["xg"], q["yh"], q["xd"], q["yb"],
                             _rgb(couleurs[lieu])))
        geo["textes"].append((q["xd"] + 8, (q["yh"] + q["yb"]) / 2,
                              lieu, "lm", 13, True))
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
        xc = (pos[c0]["xg"] + pos[c0]["xd"]) / 2
        geo["textes"].append((xc, -18 - 22, f"Génération {g}", "mm", 15,
                              False))
        geo["textes"].append((xc, -18 - 6, f"Total : {total_gen[g]:g}",
                              "mm", 12, False))
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
    geo.update(largeur=largeur_fig, hauteur=HAUTEUR_FIG,
               marge_bas=MARGE_BAS, titre=p["titre"])
    fig._geo = geo
    return fig


def exporter_image_pillow(geo, chemin, echelle, fmt="jpeg"):
    """Export JPEG/PNG sans kaleido ni Chrome : dessin direct avec Pillow.

    Reprend exactement la géométrie calculée pour la figure Plotly.
    """
    from PIL import Image, ImageDraw, ImageFont

    W, H = geo["largeur"], geo["hauteur"]
    # Sur-échantillonnage x2 pour le lissage, sauf image trop grande.
    ss = 2 if max(W, H) * echelle * 2 <= 9000 else 1
    k = echelle * ss
    taille = (max(1, int(W * k)), max(1, int(H * k)))

    def px(x):
        return (10 + x * (W - 20) / W) * k

    def py(y):
        return (90 + (y + 30) * (H - 100) / (H - 30)) * k

    CANDIDATES = (
        "arial.ttf", "Arial.ttf", "segoeui.ttf", "DejaVuSans.ttf",
        "LiberationSans-Regular.ttf",
        "/System/Library/Fonts/Supplemental/Arial.ttf",
        "/Library/Fonts/Arial.ttf",
        "/System/Library/Fonts/Helvetica.ttc",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/TTF/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
    )
    etat = {"chemin": None, "teste": False}

    def police(pt):
        taille_pt = max(6, int(pt * k))
        if not etat["teste"]:
            etat["teste"] = True
            for nom in CANDIDATES:
                try:
                    ImageFont.truetype(nom, 10)
                    etat["chemin"] = nom
                    break
                except OSError:
                    continue
        if etat["chemin"]:
            return ImageFont.truetype(etat["chemin"], taille_pt)
        try:                        # police intégrée, sans accents
            return ImageFont.load_default(size=taille_pt)
        except TypeError:           # Pillow < 10.1
            return ImageFont.load_default()

    def texte_sur(t):
        """Sans police système, la police intégrée n'a pas les accents."""
        police(10)
        if etat["chemin"]:
            return t
        import unicodedata
        return "".join(c for c in unicodedata.normalize("NFKD", t)
                       if not unicodedata.combining(c))

    image = Image.new("RGBA", taille, (255, 255, 255, 255))

    # Rubans : chacun dessiné sur un petit calque (boîte englobante).
    for xs, ys, (r, g, b) in geo["rubans"]:
        pts = [(px(x), py(y)) for x, y in zip(xs, ys)]
        x0 = int(min(p[0] for p in pts)) - 1
        y0 = int(min(p[1] for p in pts)) - 1
        x1 = int(max(p[0] for p in pts)) + 2
        y1 = int(max(p[1] for p in pts)) + 2
        calque = Image.new("RGBA", (x1 - x0, y1 - y0), (0, 0, 0, 0))
        ImageDraw.Draw(calque).polygon(
            [(a - x0, b_ - y0) for a, b_ in pts],
            fill=(r, g, b, int(0.45 * 255)))
        image.alpha_composite(calque, (x0, y0))

    d = ImageDraw.Draw(image)
    for xg, yh, xd, yb, (r, g, b) in geo["cases"]:
        d.rectangle([px(xg), py(yh), px(xd), py(yb)],
                    fill=(r, g, b, 255), outline=(120, 120, 120, 255),
                    width=max(1, int(k / 2)))

    for x, y, texte, ancre, pt, fond in geo["textes"]:
        texte = texte_sur(texte)
        f = police(pt)
        xx, yy = px(x), py(y)
        if fond:
            bbox = d.textbbox((xx, yy), texte, font=f, anchor=ancre)
            marge = 2 * k
            calque = Image.new("RGBA", image.size, (0, 0, 0, 0))
            ImageDraw.Draw(calque).rectangle(
                [bbox[0] - marge, bbox[1] - marge,
                 bbox[2] + marge, bbox[3] + marge],
                fill=(255, 255, 255, 190))
            image.alpha_composite(calque)
            d = ImageDraw.Draw(image)
        d.text((xx, yy), texte, font=f, fill=(51, 51, 51, 255),
               anchor=ancre)

    d.text((image.size[0] / 2, 38 * k), texte_sur(geo["titre"]), font=police(20),
           fill=(30, 30, 30, 255), anchor="mm")

    if ss > 1:
        image = image.resize((int(W * echelle), int(H * echelle)),
                             Image.LANCZOS)
    image = image.convert("RGB")
    if fmt == "png":
        image.save(chemin, "PNG", optimize=True)
    else:
        image.save(chemin, "JPEG", quality=92)


def nom_fichier_sur(texte):
    """Nettoie un texte pour en faire un nom de fichier valide partout."""
    texte = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "", texte or "")
    return re.sub(r"\s+", " ", texte).strip(" .")


def chemin_image(dossier, nom, fmt):
    """Chemin final de l'image : l'extension suit le format choisi
    (jpg ou png), quelle que soit celle que l'utilisateur a tapée."""
    nom = nom_fichier_sur(nom) or "Origine géographique"
    base, ext = os.path.splitext(nom)
    if ext.lower() in (".jpg", ".jpeg", ".png"):
        nom = base
    return os.path.join(dossier, nom + (".png" if fmt == "png" else ".jpg"))


def normaliser_chemin_depose(texte):
    """Chemin local à partir de ce que fournit un glisser-déposer ou un
    collage : chemin simple, entre guillemets, ou URI 'file:///...'
    (avec %20 pour les espaces)."""
    from urllib.parse import unquote, urlparse
    t = (texte or "").strip().strip("\"'")
    if t.lower().startswith("file:"):
        t = unquote(urlparse(t).path)
        if re.match(r"^/[A-Za-z]:", t):       # file:///C:/... (Windows)
            t = t[1:]
    return t


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

def exporter_image(fig, chemin, echelle, log, fmt="jpeg", delai=60):
    """Exporte la figure en JPEG ou PNG.

    Essaie kaleido (plotly) s'il est installé ; en cas d'échec, de
    blocage ou d'absence, bascule sur le dessin direct avec Pillow
    (aucun Chrome requis)."""
    import importlib.util
    nom = fmt.upper()

    def via_pillow():
        log(f"Export {nom} avec Pillow…")
        try:
            exporter_image_pillow(fig._geo, chemin, echelle, fmt)
            log(f"Image {nom} créée (Pillow) : {chemin}")
        except Exception:
            log(f"Échec de l'export {nom} :\n" + traceback.format_exc())

    if importlib.util.find_spec("kaleido") is None:
        via_pillow()
        return

    erreur = []

    def via_kaleido():
        try:
            fig.write_image(chemin, format=fmt, scale=echelle)
        except BaseException as e:        # noqa : on veut tout capturer
            erreur.append(e)

    t = threading.Thread(target=via_kaleido, daemon=True)
    t.start()
    t.join(delai)
    if not t.is_alive() and not erreur:
        log(f"Image {nom} créée (kaleido) : {chemin}")
        return

    if t.is_alive():
        log(f"kaleido ne répond pas après {delai} s.")
    else:
        log(f"kaleido indisponible : {erreur[0]!r}")
    via_pillow()


def generer(p, log):
    """Pipeline complet. Retourne le chemin du HTML créé."""
    individus, familles, format_lieu = lire_gedcom(p["gedcom"])
    log(f"GEDCOM relu : {len(individus)} individus, "
        f"{len(familles)} familles.")

    liens = construire_liens(
        individus, familles, p["racine"], p["nb_generations"],
        p["niveau_lieu"], p["depuis_la_fin"], p["utiliser_bapteme"],
        p["ajouter_pays"], p["pays_en_premier"], indice_pays(format_lieu),
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

    if p.get("image"):
        exporter_image(fig, p["image"], p["resolution_image"], log,
                       p["format_image"])
    return p["html"]


# ============================================================
# 6. INTERFACE GRAPHIQUE
# ============================================================

class Application(ttk.Frame):

    def __init__(self, master, dnd=False, erreur_dnd=None):
        super().__init__(master, padding=10)
        self.master = master
        self.dnd = dnd      # glisser-déposer disponible (tkinterdnd2)
        self.erreur_dnd = erreur_dnd
        master.title(f"Origines géographiques · Analyse GEDCOM  —  "
                     f"version {VERSION}")
        master.configure(bg="#eef2f7")
        master.option_add("*Font", ("DejaVu Sans", 10))
        self._configurer_style()
        self.configure(style="App.TFrame")
        self.pack(fill="both", expand=True)

        # Zone de contenu défilante : tous les réglages restent accessibles,
        # même lorsque la hauteur de l'écran est inférieure à celle de l'UI.
        self.canvas = tk.Canvas(self, highlightthickness=0, bd=0,
                                background="#eef2f7")
        self.scrollbar = ttk.Scrollbar(self, orient="vertical",
                                       command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self._maj_barre)
        self.scrollbar.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.contenu = ttk.Frame(self.canvas)
        self._fenetre_contenu = self.canvas.create_window(
            (0, 0), window=self.contenu, anchor="nw")
        self.contenu.bind("<Configure>", self._maj_zone_defilante)
        self.canvas.bind("<Configure>", self._adapter_largeur_contenu)
        # Molette : fait défiler l'interface, sauf au-dessus de la liste
        # des individus et des zones de texte (voir _lier_molette).
        self.canvas.bind_all("<MouseWheel>", self._defiler_souris)
        self.canvas.bind_all("<Button-4>", self._defiler_souris)
        self.canvas.bind_all("<Button-5>", self._defiler_souris)

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
        self.v_pays = tk.BooleanVar(value=False)
        self.v_pays_premier = tk.BooleanVar(value=False)
        self.format_lieu = None

        self.v_titre = tk.StringVar(value="Évolution des origines "
                                          "géographiques")
        self.v_px_unite = tk.DoubleVar(value=90)
        self.v_pad = tk.DoubleVar(value=24)
        self.v_facteur = tk.DoubleVar(value=1.25)
        self.v_larg_noeud = tk.DoubleVar(value=22)
        self.v_esp_col = tk.DoubleVar(value=260)

        self.v_html = tk.StringVar()
        self.v_img_on = tk.BooleanVar(value=False)
        self.v_format = tk.StringVar(value="jpg")
        self.v_nom_image = tk.StringVar()
        self.v_dossier_image = tk.StringVar()
        self.v_resolution = tk.DoubleVar(value=2)
        self._nom_image_auto = ""
        self.v_csv_on = tk.BooleanVar(value=False)
        self.v_ouvrir = tk.BooleanVar(value=True)

        self._construire_ui()
        for v in (self.v_niveau, self.v_sens, self.v_pays,
                  self.v_pays_premier):
            v.trace_add("write", lambda *a: self._maj_apercu_lieux())
        self.v_pays.trace_add("write", lambda *a: self._maj_etat_pays())
        self._maj_etat_pays()
        for v in (self.v_img_on, self.v_format, self.v_nom_image,
                  self.v_dossier_image):
            v.trace_add("write", lambda *a: self._maj_section_image())
        self._maj_section_image()
        self.v_recherche.trace_add("write", lambda *a: self._filtrer())
        if self.dnd:
            self._activer_glisser_deposer()
        self.after(150, self._lire_logs)
        self.log(f"Origines géographiques · version {VERSION}")
        if self.erreur_dnd:
            self.log("Glisser-déposer indisponible : " + self.erreur_dnd)
        elif self.dnd and sys.platform.startswith("linux") and (
                os.environ.get("WAYLAND_DISPLAY")
                or os.environ.get("XDG_SESSION_TYPE") == "wayland"):
            self.log("Session Wayland détectée : si le glisser-déposer ne "
                     "réagit pas, collez le chemin du fichier dans le "
                     "champ « Fichier GEDCOM » puis appuyez sur Entrée.")

    def _maj_section_image(self):
        """Active / désactive les champs de l'image et affiche le chemin
        final (l'extension suit le format choisi)."""
        etat = "normal" if self.v_img_on.get() else "disabled"
        for w in self._widgets_image:
            w.configure(state=etat)
        dossier = (self.v_dossier_image.get().strip()
                   or os.path.dirname(self.v_html.get().strip()) or ".")
        chemin = chemin_image(dossier, self.v_nom_image.get(),
                              self.v_format.get())
        self.lbl_fichier_image.configure(text=f"Fichier : {chemin}")

    def _maj_nom_image_auto(self, *_):
        """Nom proposé : « Origine géographique de <individu> ». Il suit
        la sélection tant que l'utilisateur ne l'a pas modifié."""
        x = self._xref_selectionne() if self.individus else None
        if not x:
            return
        auto = ("Origine géographique de "
                + nom_fichier_sur(self.individus[x]["nom"]))
        actuel = self.v_nom_image.get().strip()
        if not actuel or actuel == self._nom_image_auto:
            self.v_nom_image.set(auto)
        self._nom_image_auto = auto

    def _choisir_dossier_image(self):
        d = filedialog.askdirectory(
            title="Dossier de l'image",
            initialdir=self.v_dossier_image.get() or None)
        if d:
            self.v_dossier_image.set(d)

    def _maj_etat_pays(self):
        """Grise « pays en premier » tant que « ajouter le pays » n'est
        pas coché."""
        etat = "normal" if self.v_pays.get() else "disabled"
        self.chk_pays_premier.configure(state=etat)

    def _maj_barre(self, debut, fin):
        """Masque la barre de défilement quand tout tient à l'écran."""
        self.scrollbar.set(debut, fin)
        visible = bool(self.scrollbar.winfo_manager())
        if float(debut) <= 0.0 and float(fin) >= 1.0:
            if visible:
                self.scrollbar.pack_forget()
        elif not visible:
            self.scrollbar.pack(side="right", fill="y", before=self.canvas)

    def _maj_zone_defilante(self, event=None):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _adapter_largeur_contenu(self, event):
        self.canvas.itemconfigure(self._fenetre_contenu, width=event.width)

    @staticmethod
    def _pas_molette(event):
        """Nombre de lignes à faire défiler (négatif = vers le haut),
        Windows / macOS (delta) et Linux (boutons 4 et 5)."""
        if getattr(event, "num", None) == 4:
            return -3
        if getattr(event, "num", None) == 5:
            return 3
        d = int(getattr(event, "delta", 0) or 0)
        if d == 0:
            return 0
        if abs(d) >= 120:            # Windows : multiples de 120
            return -3 * int(d / 120)
        return -d                    # macOS : petites valeurs

    def _defiler_souris(self, event):
        """Défilement de l'interface entière (sauf liste et zones de
        texte, qui gèrent leur propre molette)."""
        pas = self._pas_molette(event)
        if pas and self.canvas.yview() != (0.0, 1.0):
            self.canvas.yview_scroll(pas, "units")

    def _lier_molette(self, widget):
        """Au-dessus de ce widget, la molette le fait défiler lui seul
        et ne fait plus défiler l'interface."""
        def defiler(event):
            pas = self._pas_molette(event)
            if pas:
                widget.yview_scroll(pas, "units")
            return "break"          # n'atteint pas bind_all (interface)
        for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            widget.bind(sequence, defiler)

    # ---------- glisser-déposer ----------
    def _activer_glisser_deposer(self):
        """Dépose d'un fichier .ged n'importe où dans la fenêtre."""
        from tkinterdnd2 import DND_FILES

        def enregistrer(widget):
            try:
                widget.drop_target_register(DND_FILES)
                widget.dnd_bind("<<Drop>>", self._on_depot)
            except Exception:
                pass
            for enfant in widget.winfo_children():
                enregistrer(enfant)

        enregistrer(self.master)

    def _on_depot(self, event):
        try:
            elements = list(self.tk.splitlist(event.data or ""))
        except tk.TclError:
            elements = (event.data or "").split()
        chemins = [normaliser_chemin_depose(x) for x in elements]
        chemins = [c for c in chemins if c]
        if not chemins:
            self.log("Dépôt reçu sans fichier (données vides). Utilisez "
                     "« Parcourir… » ou collez le chemin du fichier.")
            return "copy"
        chemin = chemins[0]
        self.log(f"Fichier déposé : {chemin}")
        self._ouvrir_gedcom_verifie(chemin)
        return "copy"

    def _ouvrir_gedcom_verifie(self, chemin):
        if os.path.isdir(chemin):
            messagebox.showwarning(
                "Fichier GEDCOM", "Indiquez un fichier GEDCOM, pas un "
                                  "dossier.")
            return
        if not os.path.isfile(chemin):
            messagebox.showwarning(
                "Fichier GEDCOM", f"Fichier introuvable :\n{chemin}")
            return
        if not chemin.lower().endswith((".ged", ".gedcom")):
            if not messagebox.askyesno(
                    "Fichier GEDCOM",
                    "Ce fichier n'a pas l'extension .ged ou .gedcom.\n"
                    "Essayer de le lire quand même ?"):
                return
        self._ouvrir_gedcom(chemin)

    def _charger_depuis_champ(self, *_):
        """Chemin tapé ou collé dans le champ « Fichier GEDCOM » (+ Entrée).
        Repli utile quand le glisser-déposer n'est pas disponible."""
        chemin = normaliser_chemin_depose(self.v_gedcom.get())
        if chemin:
            self._ouvrir_gedcom_verifie(chemin)

    # ---------- taille de la fenêtre ----------
    def ajuster_taille_fenetre(self):
        """Dimensionne la fenêtre sur son contenu pour que tout soit
        visible à l'ouverture (limitée à la taille de l'écran ; au-delà,
        le défilement reste disponible)."""
        self.update_idletasks()
        ecran_l = self.winfo_screenwidth()
        ecran_h = self.winfo_screenheight()
        voulu_l = (self.contenu.winfo_reqwidth()
                   + self.scrollbar.winfo_reqwidth() + 24)
        voulu_h = self.contenu.winfo_reqheight() + 24
        larg = min(voulu_l, ecran_l - 20)
        haut = min(voulu_h, ecran_h - 90)
        x = max((ecran_l - larg) // 2, 0)
        y = max((ecran_h - haut) // 2 - 30, 0)
        self.master.geometry(f"{larg}x{haut}+{x}+{y}")
        self.master.minsize(min(larg, 900), min(haut, 520))

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
        style.configure("TFrame", background=c["carte"])
        style.configure("TSeparator", background=c["bordure"])
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
        style.configure("CardTitle.TCheckbutton", background=c["carte"],
                        foreground=c["accent"], padding=(2, 0),
                        font=("DejaVu Sans", 9, "bold"))
        for nom in ("TRadiobutton", "TCheckbutton", "CardTitle.TCheckbutton"):
            style.map(nom,
                      background=[("disabled", c["carte"]),
                                  ("active", c["carte"])],
                      foreground=[("disabled", "#a3afc0")])
        style.configure("Vertical.TScrollbar", background="#e8eef8",
                        troughcolor=c["champ"], bordercolor=c["bordure"],
                        arrowsize=12)

    def _construire_ui(self):
        contenu = self.contenu
        c = self.couleurs
        contenu.configure(style="App.TFrame", padding=(16, 10))
        contenu.columnconfigure(0, weight=1, uniform="col")
        contenu.columnconfigure(1, weight=1, uniform="col")
        contenu.rowconfigure(1, weight=1)
        contenu.rowconfigure(4, weight=1)

        def carte(titre, ligne, colonne, **opts):
            f = ttk.LabelFrame(contenu, text=f"  {titre}  ",
                               style="Card.TLabelframe", padding=10)
            f.grid(row=ligne, column=colonne, sticky="nsew",
                   padx=(0, 5) if colonne == 0 else (5, 0),
                   pady=(0, 8), **opts)
            return f

        def spin(parent, var, mini, maxi, pas=1, largeur=7):
            return ttk.Spinbox(parent, from_=mini, to=maxi, increment=pas,
                               width=largeur, textvariable=var)

        # En-tête : titre, sous-titre et version
        entete = ttk.Frame(contenu, style="App.TFrame")
        entete.grid(row=0, column=0, columnspan=2, sticky="ew",
                    pady=(0, 8))
        entete.columnconfigure(0, weight=1)
        titres = ttk.Frame(entete, style="App.TFrame")
        titres.grid(row=0, column=0, sticky="w")
        ttk.Label(titres, text="Origines géographiques",
                  style="Title.TLabel").pack(anchor="w")
        ttk.Label(titres,
                  text="Explorez les lieux de naissance de vos ancêtres "
                       "à partir d’un fichier GEDCOM.",
                  style="Subtitle.TLabel").pack(anchor="w")
        ttk.Label(entete, text=f"version {VERSION}",
                  style="Subtitle.TLabel").grid(row=0, column=1,
                                                sticky="ne")

        # 1. Source et individu de départ
        f = carte("1  ·  Fichier source et individu de départ", 1, 0)
        f.columnconfigure(0, weight=1)
        f.rowconfigure(3, weight=1)
        ttk.Label(f, text="Fichier GEDCOM").grid(row=0, column=0,
                                                 columnspan=2, sticky="w")
        ligne_fichier = ttk.Frame(f)
        ligne_fichier.grid(row=1, column=0, sticky="ew", pady=(3, 8))
        ligne_fichier.columnconfigure(0, weight=1)
        champ_gedcom = ttk.Entry(ligne_fichier, textvariable=self.v_gedcom)
        champ_gedcom.grid(row=0, column=0, sticky="ew", padx=(0, 8))
        champ_gedcom.bind("<Return>", self._charger_depuis_champ)
        champ_gedcom.bind("<<Paste>>", lambda e: self.after(
            80, self._charger_depuis_champ))
        ttk.Button(ligne_fichier, text="Parcourir…",
                   command=self._choisir_gedcom).grid(row=0, column=1)

        ligne_filtre = ttk.Frame(f)
        ligne_filtre.grid(row=2, column=0, sticky="ew", pady=(0, 4))
        ligne_filtre.columnconfigure(1, weight=1)
        ttk.Label(ligne_filtre, text="Individu de départ (G1)  ·  "
                                     "filtre :").grid(row=0, column=0)
        ttk.Entry(ligne_filtre, textvariable=self.v_recherche).grid(
            row=0, column=1, sticky="ew", padx=(8, 0))

        zone = ttk.Frame(f)
        zone.grid(row=3, column=0, sticky="nsew")
        zone.columnconfigure(0, weight=1)
        zone.rowconfigure(0, weight=1)
        self.liste = tk.Listbox(
            zone, height=5, exportselection=False, activestyle="none",
            relief="flat", borderwidth=0, highlightthickness=1,
            highlightbackground=c["bordure"], highlightcolor=c["accent"],
            background="#f8fafc", foreground=c["texte"],
            selectbackground="#dbeafe", selectforeground="#1e3a8a",
            font=("DejaVu Sans", 10))
        sb = ttk.Scrollbar(zone, orient="vertical",
                           command=self.liste.yview)
        self.liste.configure(yscrollcommand=sb.set)
        self.liste.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        self._lier_molette(self.liste)
        self.liste.bind("<<ListboxSelect>>", self._maj_nom_image_auto)
        indice_dnd = ("  ·  Glissez-déposez un fichier .ged dans cette "
                      "fenêtre." if self.dnd else
                      "  ·  (glisser-déposer indisponible)")
        self.lbl_info = ttk.Label(
            f, text="Aucun fichier chargé." + indice_dnd,
            style="Muted.TLabel")
        self.lbl_info.grid(row=4, column=0, sticky="w", pady=(4, 0))

        # 2. Paramètres généalogiques
        g = carte("2  ·  Ascendance et lieux", 1, 1)
        g.columnconfigure(0, weight=1)
        g.rowconfigure(8, weight=1)

        ligne = ttk.Frame(g)
        ligne.grid(row=0, column=0, sticky="ew")
        ligne.columnconfigure(0, weight=1, uniform="reglage")
        ligne.columnconfigure(2, weight=1, uniform="reglage")
        gauche = ttk.Frame(ligne)
        gauche.grid(row=0, column=0, sticky="w")
        ttk.Label(gauche, text="Nombre de générations (G1 incluse)").pack(
            anchor="w")
        spin(gauche, self.v_nb_gen, 2, 30).pack(anchor="w", pady=(3, 0))
        ttk.Separator(ligne, orient="vertical").grid(
            row=0, column=1, sticky="ns", padx=14)
        droite = ttk.Frame(ligne)
        droite.grid(row=0, column=2, sticky="w")
        ttk.Label(droite, text="Niveau du lieu à retenir").pack(anchor="w")
        spin(droite, self.v_niveau, 1, 10).pack(anchor="w", pady=(3, 0))

        ttk.Radiobutton(g, text="Compter depuis le début (commune = 1)",
                        variable=self.v_sens, value="debut").grid(
            row=1, column=0, sticky="w", pady=(6, 0))
        ttk.Radiobutton(g, text="Compter depuis la fin (pays = 1)",
                        variable=self.v_sens, value="fin").grid(
            row=2, column=0, sticky="w")
        ttk.Checkbutton(g, text="Utiliser le baptême si naissance absente",
                        variable=self.v_bapteme).grid(
            row=3, column=0, sticky="w")
        ttk.Checkbutton(g, text="Ajouter le pays (séparé par un tiret)",
                        variable=self.v_pays).grid(
            row=4, column=0, sticky="w")
        self.chk_pays_premier = ttk.Checkbutton(
            g, text="Pays en premier (décoché : pays en dernier)",
            variable=self.v_pays_premier)
        self.chk_pays_premier.grid(row=5, column=0, sticky="w",
                                   padx=(22, 0))
        ttk.Label(g, text="APERÇU  ·  LIEU RETENU  ←  LIEU GEDCOM",
                  style="Muted.TLabel").grid(
            row=6, column=0, sticky="w", pady=(6, 3))
        self.apercu = tk.Text(
            g, height=6, width=42, wrap="word", state="disabled",
            background="#f8fafc", foreground=c["texte"],
            relief="flat", borderwidth=0, padx=9, pady=6,
            highlightthickness=1, highlightbackground=c["bordure"],
            font=("DejaVu Sans", 9))
        self.apercu.grid(row=8, column=0, sticky="nsew")
        self._lier_molette(self.apercu)

        # 3. Apparence du diagramme
        a = carte("3  ·  Apparence du diagramme", 2, 0)
        a.columnconfigure(1, weight=1)
        a.columnconfigure(3, weight=1)
        ttk.Label(a, text="Titre du diagramme").grid(row=0, column=0,
                                                     sticky="w")
        ttk.Entry(a, textvariable=self.v_titre).grid(
            row=0, column=1, columnspan=3, sticky="ew", padx=(8, 0))
        champs = [
            ("Pixels par individu", self.v_px_unite, 10, 500, 5),
            ("Écart entre les cases (px)", self.v_pad, 0, 200, 2),
            ("Atténuation (× par doublement)", self.v_facteur,
             1.0, 2.0, 0.05),
            ("Largeur d’une case (px)", self.v_larg_noeud, 4, 100, 2),
            ("Distance entre générations (px)", self.v_esp_col,
             80, 800, 10),
        ]
        for i, (txt, var, mini, maxi, pas) in enumerate(champs):
            r, col = 1 + i // 2, (i % 2) * 2
            ttk.Label(a, text=txt).grid(
                row=r, column=col, sticky="w", pady=(7, 0),
                padx=(0, 0) if col == 0 else (16, 0))
            spin(a, var, mini, maxi, pas, 6).grid(
                row=r, column=col + 1, sticky="w", padx=(8, 0),
                pady=(7, 0))
        ttk.Label(
            a, wraplength=520, justify="left", style="Muted.TLabel",
            text="Atténuation : 2,0 = hauteur proportionnelle à "
                 "l’effectif ; 1,25 = la hauteur augmente de 25 % quand "
                 "l’effectif double."
        ).grid(row=4, column=0, columnspan=4, sticky="w", pady=(9, 0))

        # 4. Export
        e = carte("4  ·  Export des résultats", 2, 1)
        e.columnconfigure(1, weight=1)
        ttk.Label(e, text="Fichier HTML").grid(row=0, column=0, sticky="w")
        ttk.Entry(e, textvariable=self.v_html).grid(
            row=0, column=1, sticky="ew", padx=8)
        ttk.Button(e, text="Choisir…", command=self._choisir_html).grid(
            row=0, column=2)

        # Section image : activée / désactivée par sa case à cocher
        case_image = ttk.Checkbutton(
            e, text="Créer une image", variable=self.v_img_on,
            style="CardTitle.TCheckbutton")
        img = ttk.LabelFrame(e, labelwidget=case_image,
                             style="Card.TLabelframe", padding=(10, 6))
        img.grid(row=1, column=0, columnspan=3, sticky="ew", pady=(8, 0))
        img.columnconfigure(1, weight=1)
        ligne_fmt = ttk.Frame(img)
        ligne_fmt.grid(row=0, column=0, columnspan=3, sticky="w")
        ttk.Label(ligne_fmt, text="Format").pack(side="left")
        r_jpg = ttk.Radiobutton(ligne_fmt, text="JPG",
                                variable=self.v_format, value="jpg")
        r_jpg.pack(side="left", padx=(8, 0))
        r_png = ttk.Radiobutton(ligne_fmt, text="PNG",
                                variable=self.v_format, value="png")
        r_png.pack(side="left", padx=(4, 22))
        ttk.Label(ligne_fmt, text="Résolution (×)").pack(side="left")
        sp_res = spin(ligne_fmt, self.v_resolution, 1, 6, 0.5, 5)
        sp_res.pack(side="left", padx=(8, 0))
        ttk.Label(img, text="Nom").grid(row=1, column=0, sticky="w",
                                        pady=(6, 0))
        champ_nom = ttk.Entry(img, textvariable=self.v_nom_image)
        champ_nom.grid(row=1, column=1, sticky="ew", padx=8, pady=(6, 0))
        btn_dossier = ttk.Button(img, text="Dossier…",
                                 command=self._choisir_dossier_image)
        btn_dossier.grid(row=1, column=2, pady=(6, 0))
        self.lbl_fichier_image = ttk.Label(
            img, style="Muted.TLabel", wraplength=470, justify="left")
        self.lbl_fichier_image.grid(row=2, column=0, columnspan=3,
                                    sticky="w", pady=(4, 0))
        self._widgets_image = [r_jpg, r_png, sp_res, champ_nom, btn_dossier]

        opts = ttk.Frame(e)
        opts.grid(row=2, column=0, columnspan=3, sticky="w", pady=(6, 0))
        ttk.Checkbutton(opts, text="Liens en CSV (Excel)",
                        variable=self.v_csv_on).pack(side="left",
                                                     padx=(0, 18))
        ttk.Checkbutton(opts, text="Ouvrir le HTML à la fin",
                        variable=self.v_ouvrir).pack(side="left")

        # Lancement et journal
        self.btn = ttk.Button(contenu, text="GÉNÉRER LE DIAGRAMME",
                              style="Primary.TButton", command=self._lancer)
        self.btn.grid(row=3, column=0, columnspan=2, sticky="ew",
                      pady=(0, 8))
        journal_card = ttk.LabelFrame(
            contenu, text="  Journal  ·  Suivi de la génération  ",
            style="Card.TLabelframe", padding=8)
        journal_card.grid(row=4, column=0, columnspan=2, sticky="nsew")
        journal_card.columnconfigure(0, weight=1)
        journal_card.rowconfigure(0, weight=1)
        self.journal = tk.Text(
            journal_card, height=4, state="disabled", wrap="word",
            background="#f8fafc", foreground="#475569", relief="flat",
            borderwidth=0, padx=8, pady=5, font=("DejaVu Sans Mono", 9),
            highlightthickness=1, highlightbackground=c["bordure"])
        self.journal.grid(row=0, column=0, sticky="nsew")
        journal_sb = ttk.Scrollbar(journal_card, orient="vertical",
                                   command=self.journal.yview)
        journal_sb.grid(row=0, column=1, sticky="ns")
        self.journal.configure(yscrollcommand=journal_sb.set)
        self._lier_molette(self.journal)

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
        self._ouvrir_gedcom(chemin)

    def _ouvrir_gedcom(self, chemin):
        """Choisi par « Parcourir » ou déposé dans la fenêtre."""
        self.v_gedcom.set(chemin)
        base = os.path.splitext(chemin)[0]
        self.v_html.set(base + "_sankey.html")
        self.v_dossier_image.set(os.path.dirname(chemin))
        self._charger(chemin)

    def _charger(self, chemin):
        try:
            (self.individus, self.familles,
             self.format_lieu) = lire_gedcom(chemin)
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
        self.log(f"Fichier chargé : {os.path.basename(chemin)}")
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
        self._maj_nom_image_auto()

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
                retenu = extraire_lieu(
                    brut, niveau, self.v_sens.get() == "fin",
                    self.v_pays.get(), self.v_pays_premier.get(),
                    indice_pays(self.format_lieu))
                lignes.append(f"{retenu}  ←  {brut}")
            if len(lignes) >= 12:
                break
        contenu = "\n".join(lignes) or "(aucun lieu)"
        self.apercu.configure(state="normal")
        self.apercu.delete("1.0", "end")
        self.apercu.insert("end", contenu)
        self.apercu.configure(state="disabled")

    # ---------- choix de fichiers de sortie ----------
    def _choisir_html(self):
        c = filedialog.asksaveasfilename(
            defaultextension=".html", initialfile=os.path.basename(
                self.v_html.get() or "diagramme_sankey.html"),
            filetypes=[("HTML", "*.html")])
        if c:
            self.v_html.set(c)

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
                ajouter_pays=self.v_pays.get(),
                pays_en_premier=self.v_pays_premier.get(),
                titre=self.v_titre.get(),
                pixels_par_unite=float(self.v_px_unite.get()),
                pad_noeuds=float(self.v_pad.get()),
                facteur_doublement=float(self.v_facteur.get()),
                largeur_noeud=float(self.v_larg_noeud.get()),
                espace_colonnes=float(self.v_esp_col.get()),
                html=self.v_html.get().strip(),
                image=None,
                format_image=("png" if self.v_format.get() == "png"
                              else "jpeg"),
                resolution_image=float(self.v_resolution.get()),
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
        if self.v_img_on.get():
            dossier = (self.v_dossier_image.get().strip()
                       or os.path.dirname(p["html"]) or ".")
            if not os.path.isdir(dossier):
                raise ValueError(
                    f"Le dossier de l'image n'existe pas :\n{dossier}")
            p["image"] = chemin_image(dossier, self.v_nom_image.get(),
                                      self.v_format.get())
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
    import importlib.util
    for nom in ("numpy", "plotly"):
        # find_spec ne charge pas le module : démarrage immédiat.
        if importlib.util.find_spec(nom) is None:
            manquants.append(nom)
    return manquants


def creer_fenetre(racine, dnd=False, erreur_dnd=None):
    """Construit l'application et dimensionne la fenêtre sur son
    contenu (tout est visible à l'ouverture)."""
    app = Application(racine, dnd=dnd, erreur_dnd=erreur_dnd)
    app.ajuster_taille_fenetre()
    return app


def creer_racine():
    """Fenêtre principale, avec glisser-déposer si tkinterdnd2 est
    utilisable. Retourne (racine, dnd_disponible, message_erreur)."""
    try:
        from tkinterdnd2 import TkinterDnD
    except ImportError:
        return tk.Tk(), False, ("module tkinterdnd2 non installé "
                                "(pip install tkinterdnd2)")
    try:
        return TkinterDnD.Tk(), True, None
    except Exception as e:      # bibliothèque tkdnd absente / incompatible
        try:                    # ferme la fenêtre créée à moitié
            if tk._default_root is not None:
                tk._default_root.destroy()
        except Exception:
            pass
        return tk.Tk(), False, (f"{type(e).__name__}: {e} "
                                "(essayez pip install -U tkinterdnd2)")


def main():
    if any(a in ("--version", "-V") for a in sys.argv[1:]):
        print(f"Origines géographiques · Analyse GEDCOM — version {VERSION}")
        return

    racine, dnd, erreur_dnd = creer_racine()

    manquants = verifier_dependances()
    if manquants:
        messagebox.showerror(
            "Modules manquants",
            "Modules Python à installer :\n\n"
            f"    pip install {' '.join(manquants)}\n\n"
            "(et, pour l'export JPG / PNG : pip install pillow ;\n"
            "pour le glisser-déposer : pip install tkinterdnd2)")
        racine.destroy()
        sys.exit(1)

    creer_fenetre(racine, dnd, erreur_dnd)
    racine.mainloop()


if __name__ == "__main__":
    main()
