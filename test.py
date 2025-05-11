import re
from copy import deepcopy
from sympy import to_cnf, symbols
from collections import Counter

simboluri = {chr(c): symbols(chr(c)) for c in range(ord('A'), ord('Z') + 1)}

def tokenizare(formula):
    return re.findall(r'¬|→|↔|∧|∨|\(|\)|[A-Z]', formula.replace(" ", ""))

def este_fbf(formula):
    tokeni = tokenizare(formula)
    poz = 0

    def expr():
        nonlocal poz
        if poz >= len(tokeni): return False
        t = tokeni[poz]

        if t == '¬':
            poz += 1
            return expr()
        elif t == '(':
            poz += 1
            if not expr(): return False
            if poz >= len(tokeni) or tokeni[poz] not in {'∧', '∨', '→', '↔'}: return False
            poz += 1
            if not expr(): return False
            if poz >= len(tokeni) or tokeni[poz] != ')': return False
            poz += 1
            return True
        elif re.fullmatch(r'[A-Z]', t):
            poz += 1
            return True
        return False

    rezultat = expr()
    return rezultat and poz == len(tokeni)

def converteste_in_cnf(expr):
    expr = expr.replace("¬", "~").replace("∧", "&").replace("∨", "|").replace("→", ">>").replace("↔", "<<")
    try:
        return str(to_cnf(eval(expr, {}, simboluri)))
    except:
        return None

def parseaza_cnf(text_cnf):
    text_cnf = text_cnf.replace("(", "").replace(")", "")
    return [[lit.strip() for lit in clauza.split("|")] for clauza in text_cnf.split(" & ")]

def la_clauze_int(clauze):
    mapa, nr, rezultat = {}, 1, []
    for clauza in clauze:
        c_int = []
        for lit in clauza:
            neg = lit.startswith("~")
            v = lit[1:] if neg else lit
            if v not in mapa:
                mapa[v] = nr
                nr += 1
            c_int.append(-mapa[v] if neg else mapa[v])
        rezultat.append(c_int)
    return rezultat, mapa

def afiseaza_clauze_litere(clauze_int, mapa):
    invers = {v: k for k, v in mapa.items()}
    return [[f"¬{invers[abs(l)]}" if l < 0 else invers[abs(l)] for l in clauza] for clauza in clauze_int]

def dpll_atribuire(clauze, atrib=[]):
    if not clauze: return True, atrib
    if [] in clauze: return False, []

    unit = [c[0] for c in clauze if len(c) == 1]
    if unit:
        return dpll_atribuire(simplifica(clauze, unit[0]), atrib + [unit[0]])

    frecvente = Counter(l for cl in clauze for l in cl)
    lit_best = frecvente.most_common(1)[0][0]

    ok, a = dpll_atribuire(simplifica(clauze, lit_best), atrib + [lit_best])
    if ok:
        return True, a
    return dpll_atribuire(simplifica(clauze, -lit_best), atrib + [-lit_best])

def simplifica(clauze, lit):
    noi = []
    for c in clauze:
        if lit in c:
            continue
        noi.append([l for l in c if l != -lit])
    return noi

def rezolutie(clauze):
    clauze = [frozenset(c) for c in clauze]
    multime = set(clauze)
    while True:
        noi = set()
        perechi = [(cl1, cl2) for i, cl1 in enumerate(clauze) for j, cl2 in enumerate(clauze) if i < j]
        for cl1, cl2 in perechi:
            for l in cl1:
                if -l in cl2:
                    rez = (cl1 - {l}) | (cl2 - {-l})
                    if not rez: return False
                    noi.add(frozenset(rez))
        if noi.issubset(multime): return True
        multime |= noi
        clauze = list(multime)

def davis_putnam(clauze):
    atrib = []
    variabile = set(abs(l) for cl in clauze for l in cl)
    def elimina(v):
        poz, neg, rest = [], [], []
        for c in clauze:
            if v in c: poz.append(c)
            elif -v in c: neg.append(c)
            else: rest.append(c)
        noi = rest[:]
        for p in poz:
            for n in neg:
                r = list(set(p + n) - {v, -v})
                if not r: return None
                noi.append(r)
        return noi
    for v in variabile:
        rezultat = elimina(v)
        if rezultat is None:
            return False, []
        clauze = rezultat
        atrib.append(v)
    return True, atrib

def alegere_solver(clauze_int):
    total = len(clauze_int)
    unitare = [c for c in clauze_int if len(c) == 1]
    raport = len(unitare) / total if total > 0 else 0
    contor = Counter(l for c in clauze_int for l in c)
    pure = [l for l in contor if -l not in contor]

    if raport > 0.35:
        return "DPLL", ["Frecvență mare de clauze unitare"]
    if pure:
        return "DP", ["Prezență de litere pure"]
    return "DPLL", ["Situație implicită: DPLL"]

def testeaza_formula(formula):
    print(f"\n")
    print(f" Analizăm formula: {formula}")
    print(f"")

    if not este_fbf(formula):
        print("✘ Această expresie nu este bine formată (FBF invalid).")
        return

    cnf = converteste_in_cnf(formula)
    if cnf is None:
        print("✘ Eroare în conversia la formă normală conjunctivă.")
        return

    print("Formă CNF:", cnf.replace("&", "∧").replace("|", "∨").replace("~", "¬"))
    clauze = parseaza_cnf(cnf)
    clauze_int, mapa = la_clauze_int(clauze)
    print("Clauze extrase:")
    for c in afiseaza_clauze_litere(clauze_int, mapa):
        print("  •", c)

    solver, motive = alegere_solver(clauze_int)
    print(f"\n🧠 Se propune folosirea metodei: {solver}")
    for m in motive:
        print("   -", m)

    invers = {v: k for k, v in mapa.items()}
    def afisare_atrib(a, tag):
        print(f"\n✔ Rezultat: formula este satisfiabilă (folosind {tag})")
        print("Valori asignate variabilelor:")
        for l in a:
            print(f"   {invers[abs(l)]} = {'Adevărat' if l > 0 else 'Fals'}")

    if solver == "Resolution":
        rezultat = rezolutie(clauze_int)
        print("\n✔ Formula este satisfiabilă." if rezultat else "\n✘ Formula NU este satisfiabilă.")
    elif solver == "DP":
        rezultat, atrib = davis_putnam(deepcopy(clauze_int))
        if rezultat:
            afisare_atrib(atrib, "Davis-Putnam")
        else:
            print("\n✘ Formula NU este satisfiabilă.")
    else:
        rezultat, atrib = dpll_atribuire(deepcopy(clauze_int))
        if rezultat:
            afisare_atrib(atrib, "DPLL")
        else:
            print("\n✘ Formula NU este satisfiabilă.")

# === Teste ===
if __name__ == "__main__":
    formule = [
        "((A→B)∧(B→C))",
        "((A∧B)→(C∨D))",
        "(¬(A∨B))",
        "((A→B)∧(B→C)∧(C→D))",
        "(A↔(¬B))",
        "((A∨B)∧(¬A∨¬B))",
        "(((A→B)∧(B→C))∧A)",
        "(((A↔B)∧(B↔C))∧(C↔D))",
        "((A∧(B∨C))→D)",
        "((¬A∧B)∨(C→D))",
        "(((A∨B)∧(C∨D))→(E↔F))",
        "(A→(B∧C))",
        "(¬(A∧(¬A)))",
        "((A↔B)↔C)",
        "(((A→B)∧A)→B)",
        "((A→(B→C))∧A∧B)",
        "(A↔(B∨(¬C)))",
        "((A∧B)∨(C∧D))",
        "(¬(A↔B))",
        "(((A→B)∧(C→D))∧(E→F))"
    ]
    for i, f in enumerate(formule, 1):
        print(f"\n══════════ Test #{i} ══════════")
        testeaza_formula(f)
