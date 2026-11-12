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
from tkinter import font as tkfont


# ============================================================
# 0. VERSION
# ============================================================

# Numéro de version : à changer ici à chaque publication. Il s'affiche
# en haut à droite de la fenêtre, dans son titre, et avec
#     python geo-gedcom.py --version
VERSION = "1.03"


# ============================================================
# 0 bis. THÈMES DE L'INTERFACE
# ============================================================

THEMES = {
    "clair": {
        "nom": "Clair",
        "fond": "#eef2f7", "carte": "#ffffff", "texte": "#172033",
        "secondaire": "#64748b", "accent": "#2563eb",
        "accent_survol": "#1d4ed8", "texte_accent": "#ffffff",
        "bordure": "#dbe3ee", "bordure_sub": "#e3e9f2",
        "champ": "#f8fafc", "bouton": "#e8eef8",
        "bouton_survol": "#dbe7f7", "sel_fond": "#dbeafe",
        "sel_texte": "#1e3a8a", "inactif": "#a3afc0",
        "principal_inactif": "#94a3b8",
    },
    "intermediaire": {
        "nom": "Intermédiaire",
        "fond": "#d6c8b4", "carte": "#ebe2d3", "texte": "#33271c",
        "secondaire": "#6e5b47", "accent": "#b4532a",
        "accent_survol": "#933f1c", "texte_accent": "#ffffff",
        "bordure": "#b9a78e", "bordure_sub": "#c9b9a1",
        "champ": "#f6f0e6", "bouton": "#ddd0bb",
        "bouton_survol": "#cdbda4", "sel_fond": "#f0c9a8",
        "sel_texte": "#5a2410", "inactif": "#a09079",
        "principal_inactif": "#a8987f",
    },
    "sombre": {
        "nom": "Sombre",
        "fond": "#0e131b", "carte": "#19202b", "texte": "#e5e9f0",
        "secondaire": "#97a3b6", "accent": "#6ea8ff",
        "accent_survol": "#8dbbff", "texte_accent": "#0a1120",
        "bordure": "#2f3a4b", "bordure_sub": "#2a3443",
        "champ": "#111722", "bouton": "#263042",
        "bouton_survol": "#33415a", "sel_fond": "#27487d",
        "sel_texte": "#dce9ff", "inactif": "#5a667a",
        "principal_inactif": "#3a4658",
    },
}
THEME_DEFAUT = "clair"


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


NB_NIVEAUX_DEFAUT = 5      # Commune, Code postal, Département, Région, Pays


def nombre_niveaux(index_pays):
    """Nombre de niveaux de lieu utilisables : de la commune jusqu'au
    pays inclus (5 pour « Town, Area code, County, Region, Country »)."""
    return index_pays + 1 if index_pays is not None else NB_NIVEAUX_DEFAUT


def indice_niveau(nb_parts, niveau, depuis_la_fin):
    """Position (à partir de 0) du niveau demandé dans un lieu découpé."""
    niveau = max(1, niveau)
    if depuis_la_fin:
        return max(nb_parts - niveau, 0)
    return min(niveau - 1, nb_parts - 1)


def position_pays(parts, index_pays):
    """Position du pays dans un lieu découpé, ou None.

    On utilise la position annoncée par l'en-tête du GEDCOM ; à défaut
    (ou si le lieu est trop court), on prend le dernier élément rempli.
    """
    if index_pays is not None and index_pays < len(parts):
        return index_pays
    for k in range(len(parts) - 1, -1, -1):
        if parts[k]:
            return k
    return None


def extraire_pays(parts, index_pays):
    """Pays d'un lieu déjà découpé ('' si non renseigné)."""
    k = position_pays(parts, index_pays)
    return parts[k] if k is not None else ""


def extraire_lieu(brut, niveau, depuis_la_fin, ajouter_pays=False,
                  pays_en_premier=False, index_pays=None):
    """Extrait le composant de lieu voulu dans 'Ville, CP, Dept, Pays'.

    Les composants vides sont CONSERVÉS pour ne pas décaler les niveaux :
      "Rio,,Grande Rio,Rio,BRASIL,"  -> 6 composants dont le 2e et le
      dernier sont vides. Une virgule finale signale un dernier élément
      manquant.
    Si le composant demandé est vide, le lieu est "Lieu inconnu".

    Seuls les niveaux « Commune … Pays » comptent (5 par défaut) : tout ce
    qui suit le pays (subdivision, rue, virgule finale) est ignoré. Ainsi
    « depuis la fin », le pays est toujours le niveau 1 et la commune le
    niveau 5 ; « depuis le début », la commune est 1 et le pays 5.

    niveau : 1 = premier composant (en partant de la fin ou du début).
    Si le lieu a moins de composants, on prend le plus proche.

    ajouter_pays : ajoute le pays au lieu, séparé par un tiret, avant
    (pays_en_premier) ou après. Rien n'est ajouté si le pays est vide
    ou identique au lieu retenu.
    """
    if not brut or not brut.strip():
        return LIEU_INCONNU
    parts = [p.strip() for p in brut.split(",")]
    parts = parts[:nombre_niveaux(index_pays)]
    i = indice_niveau(len(parts), niveau, depuis_la_fin)
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

    fig.write_html(p["html"], include_plotlyjs=True, full_html=True,
                   config={"displayModeBar": False, "displaylogo": False})
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
        master.option_add("*Font", ("DejaVu Sans", 10))
        self.v_theme = tk.StringVar(value=THEME_DEFAUT)
        self._configurer_style()
        self.configure(style="App.TFrame")
        self.pack(fill="both", expand=True)

        # Zone de contenu défilante : tous les réglages restent accessibles,
        # même lorsque la hauteur de l'écran est inférieure à celle de l'UI.
        self.canvas = tk.Canvas(self, highlightthickness=0, bd=0,
                                background=self.couleurs["fond"])
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
        self._messages = []        # messages de la génération en cours

        # Variables
        self.v_gedcom = tk.StringVar()
        self.v_recherche = tk.StringVar()
        self.v_nb_gen = tk.IntVar(value=8)
        self.v_niveau = tk.IntVar(value=3)
        self.v_sens = tk.StringVar(value="debut")
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
        # Toujours 2 lignes : la hauteur de la fenêtre ne bouge pas.
        dossier_aff = dossier if len(dossier) <= 58 else "…" + dossier[-57:]
        self.lbl_fichier_image.configure(
            text=f"Dossier : {dossier_aff}\n"
                 f"Fichier : {os.path.basename(chemin)}")

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

    def _maj_niveaux_lieu(self, nb):
        """Niveaux disponibles : 1 à nb (commune = 1 ... pays = nb)."""
        self.spin_niveau.configure(to=nb)
        try:
            if int(self.v_niveau.get()) > nb:
                self.v_niveau.set(nb)
        except (tk.TclError, ValueError):
            self.v_niveau.set(min(3, nb))
        self.radio_fin.configure(
            text=f"Compter depuis la fin (commune = {nb})")

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
    def ajuster_taille_fenetre(self, seulement_agrandir=False):
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
        if seulement_agrandir:
            # ne touche pas à la fenêtre si elle est déjà assez grande
            if (self.master.winfo_width() >= larg
                    and self.master.winfo_height() >= haut):
                return
            larg = max(larg, self.master.winfo_width())
            haut = max(haut, self.master.winfo_height())
            x, y = self.master.winfo_x(), self.master.winfo_y()
            x = max(min(x, ecran_l - larg), 0)
        self.master.geometry(f"{larg}x{haut}+{x}+{y}")
        self.master.minsize(min(larg, 900), min(haut, 520))

    # ---------- style et construction ----------
    def _configurer_style(self):
        """Prépare ttk (thème « clam ») puis applique le thème choisi."""
        self.style = ttk.Style(self.master)
        try:
            self.style.theme_use("clam")
        except tk.TclError:
            pass
        self.couleurs = THEMES[THEME_DEFAUT]
        self._appliquer_theme(THEME_DEFAUT)

    def _appliquer_theme(self, cle):
        """Applique un thème : styles ttk + widgets Tk classiques."""
        if cle not in THEMES:
            cle = THEME_DEFAUT
        self.couleurs = c = THEMES[cle]
        style = self.style
        self.master.configure(bg=c["fond"])

        style.configure(".", background=c["carte"], foreground=c["texte"],
                        fieldbackground=c["champ"],
                        bordercolor=c["bordure"],
                        lightcolor=c["carte"], darkcolor=c["carte"],
                        troughcolor=c["champ"], focuscolor=c["carte"],
                        insertcolor=c["texte"], arrowcolor=c["texte"])
        style.configure("App.TFrame", background=c["fond"])
        style.configure("TFrame", background=c["carte"])
        style.configure("TSeparator", background=c["bordure"])
        style.configure("Card.TLabelframe", background=c["carte"],
                        bordercolor=c["bordure"], relief="solid",
                        borderwidth=1)
        style.configure("Sub.TLabelframe", background=c["carte"],
                        bordercolor=c["bordure_sub"], relief="solid",
                        borderwidth=1)
        style.configure("Sub.TLabelframe.Label", background=c["carte"],
                        foreground=c["secondaire"],
                        font=("DejaVu Sans", 9, "bold"))
        style.configure("Card.TLabelframe.Label", background=c["carte"],
                        foreground=c["accent"],
                        font=("DejaVu Sans", 10, "bold"))
        style.configure("TLabel", background=c["carte"],
                        foreground=c["texte"])
        style.configure("Muted.TLabel", background=c["carte"],
                        foreground=c["secondaire"], font=("DejaVu Sans", 9))
        style.configure("Status.TLabel", background=c["fond"],
                        foreground=c["secondaire"], font=("DejaVu Sans", 9))
        style.configure("Title.TLabel", background=c["fond"],
                        foreground=c["texte"], font=("DejaVu Sans", 19, "bold"))
        style.configure("Subtitle.TLabel", background=c["fond"],
                        foreground=c["secondaire"], font=("DejaVu Sans", 10))
        style.configure("TEntry", fieldbackground=c["champ"],
                        foreground=c["texte"], bordercolor=c["bordure"],
                        insertcolor=c["texte"], padding=(8, 7))
        style.configure("TSpinbox", fieldbackground=c["champ"],
                        foreground=c["texte"], bordercolor=c["bordure"],
                        background=c["bouton"], arrowcolor=c["texte"],
                        insertcolor=c["texte"], padding=(6, 5), arrowsize=12)
        style.map("TEntry", fieldbackground=[("disabled", c["carte"])],
                  foreground=[("disabled", c["inactif"])])
        style.map("TSpinbox", fieldbackground=[("disabled", c["carte"])],
                  foreground=[("disabled", c["inactif"])])
        style.configure("TButton", background=c["bouton"],
                        foreground=c["texte"], bordercolor=c["bordure"],
                        padding=(12, 7), font=("DejaVu Sans", 9, "bold"))
        style.map("TButton",
                  background=[("disabled", c["carte"]),
                              ("active", c["bouton_survol"])],
                  foreground=[("disabled", c["inactif"])])
        style.configure("Primary.TButton", background=c["accent"],
                        foreground=c["texte_accent"],
                        bordercolor=c["accent"], padding=(14, 11),
                        font=("DejaVu Sans", 10, "bold"))
        style.map("Primary.TButton",
                  background=[("active", c["accent_survol"]),
                              ("disabled", c["principal_inactif"])],
                  foreground=[("disabled", c["carte"])])
        for nom, fond in (("TRadiobutton", c["carte"]),
                          ("TCheckbutton", c["carte"]),
                          ("CardTitle.TCheckbutton", c["carte"]),
                          ("Theme.TRadiobutton", c["fond"])):
            style.configure(nom, background=fond, foreground=c["texte"],
                            indicatorbackground=c["champ"],
                            indicatorforeground=c["accent"],
                            upperbordercolor=c["secondaire"],
                            lowerbordercolor=c["secondaire"],
                            padding=(3, 5))
            style.map(nom,
                      background=[("disabled", fond), ("active", fond)],
                      foreground=[("disabled", c["inactif"])],
                      indicatorbackground=[("disabled", c["carte"]),
                                           ("pressed", c["champ"])],
                      indicatorforeground=[("disabled", c["inactif"])])
        style.configure("CardTitle.TCheckbutton", foreground=c["accent"],
                        padding=(2, 0), font=("DejaVu Sans", 9, "bold"))
        style.configure("Vertical.TScrollbar", background=c["bouton"],
                        troughcolor=c["champ"], bordercolor=c["bordure"],
                        arrowcolor=c["texte"], arrowsize=12)
        style.map("Vertical.TScrollbar",
                  background=[("active", c["bouton_survol"])])

        # Widgets Tk classiques (créés plus tard ou déjà présents)
        if hasattr(self, "canvas"):
            self.canvas.configure(background=c["fond"])
        if hasattr(self, "liste"):
            self.liste.configure(
                background=c["champ"], foreground=c["texte"],
                highlightbackground=c["bordure"],
                highlightcolor=c["accent"],
                selectbackground=c["sel_fond"],
                selectforeground=c["sel_texte"])
        if hasattr(self, "apercu"):
            self.apercu.configure(
                background=c["champ"], foreground=c["texte"],
                highlightbackground=c["bordure"])
            self.apercu.tag_configure("choisi", background=c["sel_fond"],
                                      foreground=c["sel_texte"])

    def _changer_theme(self):
        self._appliquer_theme(self.v_theme.get())

    def _construire_ui(self):
        contenu = self.contenu
        c = self.couleurs
        contenu.configure(style="App.TFrame", padding=(16, 10))
        contenu.columnconfigure(0, weight=1)
        contenu.columnconfigure(1, weight=1)
        contenu.rowconfigure(1, weight=1)

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
        droite = ttk.Frame(entete, style="App.TFrame")
        droite.grid(row=0, column=1, sticky="ne")
        ttk.Label(droite, text=f"version {VERSION}",
                  style="Subtitle.TLabel").grid(row=0, column=0,
                                                columnspan=4, sticky="e")
        ttk.Label(droite, text="Thème :",
                  style="Subtitle.TLabel").grid(row=1, column=0,
                                                padx=(0, 4))
        for k, cle in enumerate(THEMES):
            ttk.Radiobutton(droite, text=THEMES[cle]["nom"],
                            value=cle, variable=self.v_theme,
                            style="Theme.TRadiobutton",
                            command=self._changer_theme
                            ).grid(row=1, column=k + 1, padx=2)

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
            background=c["champ"], foreground=c["texte"],
            selectbackground=c["sel_fond"], selectforeground=c["sel_texte"],
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

        # 2. Ascendance et lieux, en sous-sections
        g = carte("2  ·  Ascendance et lieux", 1, 1)
        g.columnconfigure(0, weight=2, uniform="sec2")
        g.columnconfigure(1, weight=3, uniform="sec2")
        g.rowconfigure(2, weight=1)

        def sous(titre, ligne, colonne, **opts):
            f = ttk.LabelFrame(g, text=f" {titre} ", style="Sub.TLabelframe",
                               padding=(10, 4, 10, 6))
            f.grid(row=ligne, column=colonne, sticky="nsew",
                   padx=(0, 4) if colonne == 0 else (4, 0),
                   pady=(0, 6), **opts)
            return f

        # Ascendance
        asc = sous("Ascendance", 0, 0)
        ttk.Label(asc, text="Nombre de générations").pack(anchor="w")
        ligne_gen = ttk.Frame(asc)
        ligne_gen.pack(anchor="w", pady=(3, 0))
        spin(ligne_gen, self.v_nb_gen, 2, 30).pack(side="left")
        ttk.Label(ligne_gen, text="G1 incluse",
                  style="Muted.TLabel").pack(side="left", padx=(8, 0))

        # Pays
        pays = sous("Pays", 1, 0)
        ttk.Checkbutton(pays, text="Ajouter le pays",
                        variable=self.v_pays).pack(anchor="w")
        self.chk_pays_premier = ttk.Checkbutton(
            pays, text="Pays en premier", variable=self.v_pays_premier)
        self.chk_pays_premier.pack(anchor="w", padx=(22, 0))
        ttk.Label(pays, text="Séparé du lieu par un tiret.\n"
                             "Décoché : pays en dernier.",
                  style="Muted.TLabel", justify="left").pack(
            anchor="w", pady=(3, 0))

        # Lieu retenu
        lieu = sous("Lieu retenu", 0, 1, rowspan=2)
        ttk.Label(lieu, text="Niveau du lieu à retenir").pack(anchor="w")
        self.spin_niveau = spin(lieu, self.v_niveau, 1, NB_NIVEAUX_DEFAUT)
        self.spin_niveau.pack(anchor="w", pady=(3, 6))
        ttk.Radiobutton(lieu, text="Compter depuis le début (commune = 1)",
                        variable=self.v_sens, value="debut").pack(
            anchor="w")
        self.radio_fin = ttk.Radiobutton(
            lieu, variable=self.v_sens, value="fin")
        self.radio_fin.pack(anchor="w")
        self._maj_niveaux_lieu(NB_NIVEAUX_DEFAUT)
        ttk.Separator(lieu, orient="horizontal").pack(fill="x",
                                                      pady=(6, 4))
        ttk.Checkbutton(lieu, text="Utiliser le baptême si naissance "
                                   "absente",
                        variable=self.v_bapteme).pack(anchor="w")

        # Aperçu
        ap = sous("Aperçu  ·  lieu retenu  ←  lieu du GEDCOM", 2, 0,
                  columnspan=2)
        ap.grid_configure(padx=0, pady=0)
        ap.columnconfigure(0, weight=1)
        ap.rowconfigure(0, weight=1)
        self.apercu = tk.Text(
            ap, height=6, width=42, wrap="none", state="disabled",
            background=c["champ"], foreground=c["texte"],
            relief="flat", borderwidth=0, padx=9, pady=6,
            highlightthickness=1, highlightbackground=c["bordure"],
            font=("DejaVu Sans", 9))
        self.apercu.tag_configure("choisi", background=c["sel_fond"],
                                  foreground=c["sel_texte"])
        self.apercu.grid(row=0, column=0, sticky="nsew")
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
            img, style="Muted.TLabel", justify="left")
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

        # Lancement
        self.btn = ttk.Button(contenu, text="GÉNÉRER LE DIAGRAMME",
                              style="Primary.TButton", command=self._lancer)
        self.btn.grid(row=3, column=0, columnspan=2, sticky="ew",
                      pady=(0, 6))
        # Ligne d'état (une seule ligne : dernier message important)
        self.lbl_statut = ttk.Label(contenu, text="", anchor="w",
                                    style="Status.TLabel")
        self.lbl_statut.grid(row=4, column=0, columnspan=2, sticky="ew")

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
                    self._noter(msg)
        except queue.Empty:
            pass
        self.after(150, self._lire_logs)

    def _noter(self, msg):
        """Garde le message et affiche sa première ligne dans la ligne
        d'état."""
        self._messages.append(msg)
        lignes = msg.strip().splitlines()
        premiere = lignes[0] if lignes else ""
        if len(premiere) > 160:
            premiere = premiere[:157] + "…"
        self.lbl_statut.configure(text=premiere)

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
        self._maj_niveaux_lieu(nombre_niveaux(indice_pays(self.format_lieu)))
        self.log(f"Fichier chargé : {os.path.basename(chemin)}")
        self.v_recherche.set("")
        self._filtrer(selection=self.premier)
        self._maj_apercu_lieux()
        self._dimensionner_apercu()

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

    def _dimensionner_apercu(self):
        """Élargit l'aperçu (donc la fenêtre) pour que chaque ligne tienne
        sur une seule ligne, quel que soit le niveau de lieu choisi."""
        if not self.individus:
            return
        police = tkfont.Font(font=self.apercu.cget("font"))
        ip = indice_pays(self.format_lieu)
        nb = nombre_niveaux(ip)
        largeur = 0
        vus = set()
        for indi in self.individus.values():
            brut = indi["lieu_naissance"] or indi["lieu_bapteme"]
            if not brut or brut in vus:
                continue
            vus.add(brut)
            parts = [p.strip() for p in brut.split(",")][:nb]
            pire = (f"{extraire_pays(parts, ip)} - "
                    f"{max(parts, key=police.measure)}  ←  "
                    f"{brut}")                          # pire cas
            largeur = max(largeur, police.measure(pire))
            if len(vus) >= 12:
                break
        marge = 2 * 9 + 14           # padx du Text + liseré + ascenseur
        car = max(police.measure("0"), 1)
        self.apercu.configure(width=max(42, (largeur + marge) // car + 1))
        self.ajuster_taille_fenetre(seulement_agrandir=True)

    def _maj_apercu_lieux(self):
        """Montre comment quelques lieux du fichier seront découpés."""
        if not self.individus:
            return
        try:
            niveau = int(self.v_niveau.get())
        except (tk.TclError, ValueError):
            return
        ip = indice_pays(self.format_lieu)
        nb = nombre_niveaux(ip)
        depuis_la_fin = self.v_sens.get() == "fin"
        vus, lignes, marques = set(), [], []
        for indi in self.individus.values():
            brut = indi["lieu_naissance"] or indi["lieu_bapteme"]
            if brut and brut not in vus:
                vus.add(brut)
                retenu = extraire_lieu(
                    brut, niveau, depuis_la_fin, self.v_pays.get(),
                    self.v_pays_premier.get(), ip)
                prefixe = f"{retenu}  ←  "
                lignes.append(prefixe + brut)       # détail complet
                # éléments retenus, à surligner dans le détail
                tout = brut.split(",")
                parts = [p.strip() for p in tout][:nb]
                choisis = [indice_niveau(len(parts), niveau,
                                         depuis_la_fin)]
                if self.v_pays.get():
                    k = position_pays(parts, ip)
                    lieu = parts[choisis[0]] or LIEU_INCONNU
                    if (k is not None and parts[k]
                            and parts[k].casefold() != lieu.casefold()):
                        choisis.append(k)
                for k in choisis:
                    if k < len(tout) and tout[k].strip():
                        debut = (len(prefixe)
                                 + sum(len(t) + 1 for t in tout[:k])
                                 + len(tout[k]) - len(tout[k].lstrip()))
                        marques.append((len(lignes), debut,
                                        debut + len(tout[k].strip())))
            if len(lignes) >= 12:
                break
        self.apercu.configure(state="normal")
        self.apercu.delete("1.0", "end")
        self.apercu.insert("end", "\n".join(lignes) or "(aucun lieu)")
        for n, c0, c1 in marques:
            self.apercu.tag_add("choisi", f"{n}.{c0}", f"{n}.{c1}")
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
        self._messages = []
        self.lbl_statut.configure(text="Génération en cours…")

        def travail():
            try:
                chemin = generer(p, self.log)
                self.file_logs.put((self._fin, chemin, None))
            except Exception as e:
                self.log(traceback.format_exc())
                self.file_logs.put((self._fin, None, e))

        threading.Thread(target=travail, daemon=True).start()

    def _fin(self, chemin, erreur):
        self.btn.configure(state="normal", text="GÉNÉRER LE DIAGRAMME")
        if erreur is not None:
            self.lbl_statut.configure(text=f"Échec : {erreur}")
            messagebox.showerror("Erreur", str(erreur))
            return
        echecs = [m for m in self._messages if m.startswith("Échec")]
        if echecs:
            messagebox.showwarning("Export de l'image", "\n\n".join(echecs))
        self.lbl_statut.configure(
            text=f"Terminé : {os.path.basename(chemin)}" if chemin
            else "Terminé.")
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
    appliquer_icone(racine)
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

    if sys.platform == "win32":
        # Identité propre à l'application : la barre des tâches affiche
        # sa boussole (et non l'icône de Python).
        try:
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                "GeoGEDCOM.OriginesGeographiques")
        except Exception:
            pass

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


# ============================================================
# 8. ICÔNE DE LA FENÊTRE
# ============================================================
# Boussole (32, 48 et 64 px, PNG en base64) : intégrée au script pour la
# fenêtre et la barre des tâches. L'icône du fichier .exe / de
# l'application macOS est fournie à PyInstaller par --icon
# (boussole.ico / boussole.icns, voir build.yml).

ICONES_PNG_B64 = (
    (  # 32 px
        "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"
        "vuAIYuYhHeEAAAAASUVORK5CYII="
    ),
    (  # 48 px
        "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"
        "/wETh1LnsnB2vgAAAABJRU5ErkJggg=="
    ),
    (  # 64 px
        "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"
    ),
)


def appliquer_icone(racine):
    """Icône de la fenêtre (Windows, macOS, Linux). Retourne True/False."""
    try:
        images = [tk.PhotoImage(data="".join(b64.split()))
                  for b64 in ICONES_PNG_B64]
        racine.iconphoto(True, *images)
        racine._icones = images      # garde une référence (sinon effacées)
        return True
    except Exception:
        return False


if __name__ == "__main__":
    main()
