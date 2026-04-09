import sys
import random
from sklearn.datasets import load_breast_cancer
from sklearn.preprocessing import MinMaxScaler

# Zmuszamy Pythona do udźwignięcia strukturalnej rekurencji VOID
sys.setrecursionlimit(200000)

# ============================================================================
# DOMENA 1: ONTOLOGIA VOID (Brak liczb, tylko struktura)
# ============================================================================

class Fin: pass

class fz(Fin):
    def __repr__(self): return "fz"

class fs(Fin):
    def __init__(self, pred):
        self.pred = pred
    def __repr__(self):
        # Do debugowania wypisuje głębokość, ale strukturalnie to wciąż obiekty
        return f"fs({self.pred})"

def build_fin(n: int) -> Fin:
    """Narzędzie graniczne: konwertuje int ze świata na strukturę Fin."""
    if n <= 0: return fz()
    return fs(build_fin(n - 1))

def count_fin(f: Fin) -> int:
    """Narzędzie graniczne: mierzy strukturę do logów (odczyt darmowy)."""
    c = 0
    while isinstance(f, fs):
        c += 1
        f = f.pred
    return c

class BTrue:
    def __repr__(self): return "BTrue"
class BFalse:
    def __repr__(self): return "BFalse"
class BUnknown:
    def __repr__(self): return "BUnknown"

# ============================================================================
# DOMENA 2: FIZYKA I TERMODYNAMIKA OBLICZEŃ
# ============================================================================

def drain_budget(budget: Fin, cost: int) -> tuple[Fin, Fin]:
    """
    Fizyczne zrzucenie 'cost' warstw z budżetu. 
    Zwraca (Pozostały_Budżet, Ciepło_Wygenerowane).
    Zastosowane iteracyjnie, by uniknąć natychmiastowego C-stack overflow,
    ale idealnie odzwierciedla rekursję z Coq.
    """
    heat_ticks = 0
    current_b = budget
    while heat_ticks < cost:
        if isinstance(current_b, fz):
            return fz(), build_fin(heat_ticks) # Śmierć głodowa
        current_b = current_b.pred
        heat_ticks += 1
    return current_b, build_fin(heat_ticks)

def add_fin(n: Fin, m: Fin, budget: Fin):
    """Fizyczne dodawanie."""
    cost = count_fin(n)
    new_b, h = drain_budget(budget, cost)
    if isinstance(new_b, fz) and cost > 0:
        return fz(), fz(), h
    # Odbudowa
    res = m
    for _ in range(cost): res = fs(res)
    return res, new_b, h

def mul_fin(n: Fin, m: Fin, budget: Fin):
    """Fizyczne mnożenie to wielokrotne dodawanie."""
    iters = count_fin(n)
    val_m = count_fin(m)
    total_cost = iters * val_m
    new_b, h = drain_budget(budget, total_cost)
    if isinstance(new_b, fz) and total_cost > 0:
        return fz(), fz(), h
    return build_fin(total_cost), new_b, h

def le_fin_b3(n: Fin, m: Fin, budget: Fin):
    """Porównanie n <= m."""
    cost = min(count_fin(n), count_fin(m))
    new_b, h = drain_budget(budget, cost + 1)
    if isinstance(new_b, fz):
        return BUnknown(), fz(), h
    
    val_n = count_fin(n)
    val_m = count_fin(m)
    if val_n <= val_m:
        return BTrue(), new_b, h
    return BFalse(), new_b, h

# ============================================================================
# DOMENA 3: EPISTEMOLOGIA (FinProb i Wątpienie)
# ============================================================================

class FinProb:
    def __init__(self, num: Fin, den: Fin):
        self.num = num
        self.den = den
    def __repr__(self):
        return f"[{count_fin(self.num)}/{count_fin(self.den)}]"

def prob_le_b3(p1: FinProb, p2: FinProb, budget: Fin):
    """p1 <= p2? (a*d <= c*b). Zderzenie ułamków."""
    ad, b1, h1 = mul_fin(p1.num, p2.den, budget)
    if isinstance(b1, fz): return BUnknown(), fz(), h1
    
    cb, b2, h2 = mul_fin(p2.num, p1.den, b1)
    if isinstance(b2, fz): return BUnknown(), fz(), add_fin(h1, h2, build_fin(9999))[0]
    
    res, b3, h3 = le_fin_b3(ad, cb, b2)
    return res, b3, build_fin(count_fin(h1) + count_fin(h2) + count_fin(h3))

def add_prob_fixed(p1: FinProb, p2: FinProb, budget: Fin):
    """Dodawanie dla ułamków o tym samym mianowniku (Opcja A z audytu)."""
    num, b1, h = add_fin(p1.num, p2.num, budget)
    # Clamp do (den - 1), by nigdy nie osiągnąć absolutnego 1.0
    val_num = count_fin(num)
    val_den = count_fin(p1.den)
    if val_num >= val_den:
        val_num = val_den - 1
        num = build_fin(val_num)
    return FinProb(num, p1.den), b1, h

# ============================================================================
# DOMENA 4: RESONANT ENSEMBLE ARCHITECTURE
# ============================================================================

DENOM_INT = 16
DENOM = build_fin(DENOM_INT)
HALF = FinProb(build_fin(DENOM_INT // 2), DENOM)
ZERO_PROB = FinProb(fz(), DENOM)

class ResonantCell:
    def __init__(self, id_label, w_for, w_against, freq, init_budget):
        self.id = id_label
        # Zamrożone (Epistemologia)
        self.w_for = w_for
        self.w_against = w_against
        self.frequency = freq
        # Zmienne (Termodynamika)
        self.amplitude = HALF
        self.budget = build_fin(init_budget)
        self.heat = fz()

def is_resonant(cell: ResonantCell, input_freq: FinProb, budget: Fin):
    """Sprawdza, czy komórka reaguje na częstotliwość wejścia."""
    # Proste sprawdzenie dystansu na licznikach (zakładając wspólny mianownik 16)
    c_num = count_fin(cell.frequency.num)
    i_num = count_fin(input_freq.num)
    dist = abs(c_num - i_num)
    # Próg 4/16 (czyli 1/4 dystansu)
    b_new, h = drain_budget(budget, 3) # Koszt fizyczny percepcji odległości
    return dist <= 4, b_new

def activate_cell(cell: ResonantCell, signals: list, budget: Fin):
    """Dualny akumulator. Budowa wież FOR i AGAINST."""
    acc_for = ZERO_PROB
    acc_against = ZERO_PROB
    
    for i, s in enumerate(signals):
        if isinstance(budget, fz): break
        
        cmp, budget, _ = prob_le_b3(HALF, s, budget)
        if isinstance(cmp, BTrue):
            acc_for, budget, _ = add_prob_fixed(acc_for, cell.w_for[i], budget)
        elif isinstance(cmp, BFalse):
            acc_against, budget, _ = add_prob_fixed(acc_against, cell.w_against[i], budget)

    if isinstance(acc_for.num, fz) and isinstance(acc_against.num, fz):
        return HALF, budget

    cmp_final, budget, _ = prob_le_b3(acc_against, acc_for, budget)
    
    total, budget, _ = add_prob_fixed(acc_for, acc_against, budget)
    if isinstance(total.num, fz): return HALF, budget
    
    if isinstance(cmp_final, BTrue):
        # acc_for >= acc_against. Zwracamy dominację acc_for
        out_num = (count_fin(acc_for.num) * DENOM_INT) // max(1, count_fin(total.num))
        return FinProb(build_fin(min(out_num, DENOM_INT-1)), DENOM), budget
    else:
        # Przewaga AGAINST (sygnał < 1/2)
        out_num = (count_fin(acc_against.num) * DENOM_INT) // max(1, count_fin(total.num))
        inverted = DENOM_INT - min(out_num, DENOM_INT-1)
        return FinProb(build_fin(inverted), DENOM), budget

def resonance_cascade(active_cells, outputs, budget: Fin):
    """Konsensus fizyczny."""
    FUEL = 3 # 3 rundy kaskady
    for _ in range(FUEL):
        if isinstance(budget, fz): break
        changes = 0
        for cell_a in active_cells:
            for cell_b in active_cells:
                if cell_a.id >= cell_b.id: continue
                if isinstance(budget, fz): break
                
                a_yes = count_fin(outputs[cell_a.id].num) > DENOM_INT // 2
                b_yes = count_fin(outputs[cell_b.id].num) > DENOM_INT // 2
                
                budget, _ = drain_budget(budget, 2) # Koszt komunikacji
                
                if a_yes == b_yes:
                    # Konstruktywny rezonans (wzmocnienie reputacji)
                    amp_a = count_fin(cell_a.amplitude.num)
                    cell_a.amplitude = FinProb(build_fin(min(amp_a + 1, DENOM_INT-1)), DENOM)
                    changes += 1
                else:
                    # Destruktywny rezonans (tłumienie reputacji)
                    amp_a = count_fin(cell_a.amplitude.num)
                    cell_a.amplitude = FinProb(build_fin(max(amp_a - 1, 1)), DENOM)
                    changes += 1
        if changes == 0: break
    return budget

def verdict(active_cells, outputs, budget: Fin):
    """Głosowanie ważone amplitudą."""
    weight_for = 0
    weight_against = 0
    
    for cell in active_cells:
        amp = count_fin(cell.amplitude.num)
        if amp <= 2: continue # Zbyt słaba reputacja
        
        out_val = count_fin(outputs[cell.id].num)
        if out_val > DENOM_INT // 2:
            weight_for += amp
        elif out_val < DENOM_INT // 2:
            weight_against += amp

    budget, _ = drain_budget(budget, len(active_cells))
    
    if weight_for > weight_against:
        return BTrue(), budget
    elif weight_against > weight_for:
        return BFalse(), budget
    return BUnknown(), budget

def apply_entropia_i_nagrody(cells, outputs, truth, active_ids):
    for cell in cells:
        # Damping - Bezwzględna Entropia co epokę
        amp_val = count_fin(cell.amplitude.num)
        if amp_val > 1:
            cell.amplitude = FinProb(build_fin(amp_val - 1), DENOM)
            
        if cell.id in active_ids:
            # Credit Propagation
            out_val = count_fin(outputs[cell.id].num)
            if out_val == DENOM_INT // 2: continue # Milczenie = brak nagrody
            
            cell_yes = out_val > DENOM_INT // 2
            truth_yes = isinstance(truth, BTrue)
            
            if cell_yes == truth_yes:
                # Wypłata homeostazy z otoczenia za prawdę!
                cell.budget, _ = add_fin(cell.budget, build_fin(150), build_fin(99999))
                # Boost amplitudy za trafność
                new_amp = min(count_fin(cell.amplitude.num) + 2, DENOM_INT-1)
                cell.amplitude = FinProb(build_fin(new_amp), DENOM)

# ============================================================================
# GRANICA ŚWIATA: Wczytanie danych i uruchomienie symulacji
# ============================================================================

def main():
    print("Inicjalizacja ontologii VOID...")
    data = load_breast_cancer()
    X_raw, y_raw = data.data, data.target
    
    scaler = MinMaxScaler(feature_range=(1, DENOM_INT-1))
    X_scaled = scaler.fit_transform(X_raw)
    
    print("Tworzenie Komitetu Ekspertów (64 komórki)...")
    cells = []
    for i in range(64):
        wf = [FinProb(build_fin(random.randint(1, DENOM_INT-1)), DENOM) for _ in range(30)]
        wa = [FinProb(build_fin(random.randint(1, DENOM_INT-1)), DENOM) for _ in range(30)]
        freq_num = random.randint(4, DENOM_INT-4)
        cells.append(ResonantCell(i, wf, wa, FinProb(build_fin(freq_num), DENOM), 5000))
        
    global_budget = build_fin(100000)
    
    # Bierzemy małą próbkę (np. 50 pacjentów) na potrzeby szybkiej weryfikacji w terminalu
    # (Ze względu na koszty strukturalne, 569 pacjentów zajęłoby dużo czasu)
    SAMPLE_SIZE = 50
    X_sample = X_scaled[:SAMPLE_SIZE]
    y_sample = y_raw[:SAMPLE_SIZE]
    
    print("\n--- ROZPOCZĘCIE TRENINGU (Ewolucja Termodynamiczna) ---")
    
    for epoch in range(3): # 3 epoki wystarczą by zobaczyć śmierć i rezonans
        correct = 0
        unknowns = 0
        
        for idx in range(SAMPLE_SIZE):
            if isinstance(global_budget, fz):
                print("ŚMIERĆ CIEPLNA SIECI.")
                break
                
            # Konwersja pacjenta na sygnały FinProb
            signals = [FinProb(build_fin(int(val)), DENOM) for val in X_sample[idx]]
            truth = BTrue() if y_sample[idx] == 0 else BFalse() # 0 = malignant (BTrue), 1 = benign
            
            # 1. Attention: Kto rezonuje?
            freq_in = FinProb(build_fin(sum(int(v) for v in X_sample[idx]) // 30), DENOM)
            
            active_cells = []
            for c in cells:
                if isinstance(c.budget, fz): continue # Martwi nie słuchają
                res, c.budget = is_resonant(c, freq_in, c.budget)
                if res: active_cells.append(c)
            
            if not active_cells:
                unknowns += 1
                continue
                
            # 2. Forward Pass
            outputs = {}
            for c in active_cells:
                out, c.budget = activate_cell(c, signals, c.budget)
                outputs[c.id] = out
                
            # 3. Kaskada Konsensusu
            global_budget = resonance_cascade(active_cells, outputs, global_budget)
            
            # 4. Werdykt
            decision, global_budget = verdict(active_cells, outputs, global_budget)
            
            if isinstance(decision, BUnknown):
                unknowns += 1
            elif (isinstance(decision, BTrue) and isinstance(truth, BTrue)) or \
                 (isinstance(decision, BFalse) and isinstance(truth, BFalse)):
                correct += 1
                
            # 5. Ewolucja (Budżet i Amplituda)
            apply_entropia_i_nagrody(cells, outputs, truth, [c.id for c in active_cells])

        alive = sum(1 for c in cells if not isinstance(c.budget, fz))
        high_amp = sum(1 for c in cells if count_fin(c.amplitude.num) > DENOM_INT//2)
        print(f"Epoka {epoch+1} | Skuteczność: {correct}/{SAMPLE_SIZE-unknowns} | "
              f"BUnknown: {unknowns} | Żywe komórki: {alive}/64 | Rady Dominujące: {high_amp}")

if __name__ == "__main__":
    main()