(******************************************************************************)
(* VOID ERROR AUDIT                                                          *)
(* Discovered through Python experiments on real medical data                 *)
(* Before touching any file, know what's broken and why                       *)
(*                                                                           *)
(* Rule: express errors in Coq so the fix is already half-written            *)
(******************************************************************************)

(* ========================================================================= *)
(* ERROR 1: FinProb EXISTS                                                   *)
(* ========================================================================= *)

(* CURRENT (35 of 40 files):
   Definition FinProb := (Fin * Fin)%type.   (* num/den pair = FRACTION *)
   
   This is a rational number in disguise. VOID has no fractions.
   Fin is a finite type with inhabitants, not a numerator.
   
   AFFECTED:
     void_gates.v           — all gate definitions take FinProb
     void_perceptron.v      — Synapse has conductance : FinProb
     void_probability_minimal.v — defines FinProb, add_prob_heat, prob_le_b
     void_convergence.v     — ConvergenceMetrics uses FinProb
     void_dual_system.v     — confidence_threshold : FinProb
     void_integrated_brain.v — returns FinProb
     ... 30 more files
   
   FIX: Weight = Fin. Period.
*)

(* What it should be: *)
Definition Weight := Fin.  (* NOT a pair. NOT a fraction. A finite value. *)


(* ========================================================================= *)
(* ERROR 2: BFalse IS SILENCE                                               *)
(* ========================================================================= *)

(* CURRENT (void_perceptron.v, activate2):
   Inputs are Fin (0 or nonzero). BFalse mapped to fz = absence.
   
   The transmit function:
     | fz => (fz, fz, b', fs fz)    (* "No input = no output" *)
   
   BFalse is treated as LACK OF SIGNAL.
   But BFalse means "NO" — it's an active statement.
   A doctor saying "no tumor found" is not the same as no doctor present.
   
   Python experiment proved this: dual-accumulator where BFalse
   contributes to acc_against produced meaningful inhibition.
   Single accumulator (BTrue adds, BFalse skips) could only learn
   monotonic functions.
   
   FIX: Two accumulators. BTrue → acc_for. BFalse → acc_against.
        BUnknown → neither (honest silence).
*)

(* What it should be: *)
(*
Definition fire_dual (inputs : list Bool3)
                     (weights_for weights_against : list Fin)
                     (b : Budget)
  : (Bool3 * Budget * Heat) :=
  let (acc_for, b1)     := accumulate (filter_btrue inputs) weights_for b in
  let (acc_against, b2) := accumulate (filter_bfalse inputs) weights_against b1 in
  (* Compare two Fin values — no subtraction needed *)
  match le_fin_b3 acc_against acc_for b2 with     (* against <= for? *)
  | (BTrue, b3, h1) =>
      match le_fin_b3 acc_for acc_against b3 with (* for <= against? *)
      | (BTrue, b4, h2) => (BUnknown, b4, ...)    (* TIE = honest *)
      | _               => (BTrue, ...)            (* for wins *)
      end
  | _ => ... (* against wins or budget exhausted *)
  end.
*)


(* ========================================================================= *)
(* ERROR 3: THRESHOLD MODEL                                                  *)
(* ========================================================================= *)

(* CURRENT (void_perceptron.v, Neuron2):
   Record Neuron2 := mkNeuron2 {
     syn1 : Synapse;
     syn2 : Synapse;
     threshold : Fin          (* single threshold *)
   }.
   
   Activation: sum inputs, compare sum >= threshold.
   This is McCulloch-Pitts (1943). One accumulator, one comparison.
   
   Problem: can only learn "enough evidence FOR" but never
   "strong evidence AGAINST". A patient with 8 BFalse signals 
   and 0 BTrue looks identical to one with 8 BUnknown — both 
   give sum=0, below threshold.
   
   FIX: No threshold. Two accumulators compared directly.
        The "threshold" is implicit: who has more evidence wins.
*)

(* What it should be: *)
(*
Record PredictiveCell := mkCell {
  weights_for     : list Fin;    (* evidence weights for BTrue inputs *)
  weights_against : list Fin;    (* evidence weights for BFalse inputs *)
  budget          : Budget;      (* free energy *)
  heat            : Heat;        (* irreversible entropy *)
}.
(* No threshold field. Decision = compare acc_for vs acc_against. *)
*)


(* ========================================================================= *)
(* ERROR 4: ERODE/CONSTRICT LEARNING                                         *)
(* ========================================================================= *)

(* CURRENT (void_perceptron.v):
   Definition erode — increases synapse conductance (a FinProb!)
   Definition constrict — decreases synapse conductance
   
   Learning adjusts WEIGHTS. This requires:
     a) FinProb arithmetic (cross-multiplication for different denominators)
     b) Implicit assumption that "better weights" = "better performance"
     c) No connection to WHY the error happened
   
   This is gradient descent with extra steps.
   
   Friston/Clark insight: the brain doesn't adjust weights from errors.
   It measures PREDICTION ERROR (surprise) and pays free energy for it.
   Good predictors survive. Bad predictors die.
   
   Python proved: pure budget economics (correct=refund, wrong=penalty)
   produces natural selection. NOISE-focused cells die. BEST-focused
   cells survive. No weight adjustment needed.
   
   FIX: No erode. No constrict. Learning = budget flow.
        Correct prediction → small budget refund (precision gain)
        Wrong prediction → budget penalty (surprise cost)
        Cell death when budget=0 → natural selection
*)

(* What it should be: *)
(*
Definition prediction_update (cell : PredictiveCell) 
                             (prediction truth : Bool3)
  : PredictiveCell :=
  match bool3_eq prediction truth with
  | BTrue =>   (* CORRECT — low surprise — refund *)
      mkCell (weights_for cell) (weights_against cell)
             (add_budget (budget cell) precision_gain)
             (heat cell)
  | BFalse =>  (* WRONG — high surprise — penalty *)
      mkCell (weights_for cell) (weights_against cell)
             (sub_budget (budget cell) surprise_cost)
             (add_heat (heat cell) surprise_cost)
  | BUnknown => cell  (* can't evaluate — no change *)
  end.
*)


(* ========================================================================= *)
(* ERROR 5: SUBTRACTION EXISTS                                               *)
(* ========================================================================= *)

(* CURRENT (void_gates.v):
   Fixpoint sub_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
   
   Also: sub_saturate_b_heat in void_finite_minimal.v
   Also: complement_b (1-p) in void_gates.v
   
   VOID should not have subtraction. It implies negative number 
   thinking — "take away from". In finite types, you don't subtract.
   You COMPARE via le_fin_b3.
   
   Every use of subtraction in the codebase comes from FinProb
   arithmetic (complement, cross-multiply, divide). Remove FinProb,
   remove the need for subtraction.
   
   ONE EXCEPTION: budget penalty. But this is conceptually 
   "transfer from budget to heat" — conservation, not arithmetic.
   And it can be expressed as:
     If budget >= penalty: new_budget is (budget - penalty) levels down
     Else: budget = fz, remainder goes to heat
   This is structural, not numeric subtraction.
   
   FIX: Remove sub_fin from public API. Keep only internal
        budget_transfer for conservation law.
*)


(* ========================================================================= *)
(* ERROR 6: MULTIPLICATION FOR CROSS-MULTIPLY                                *)
(* ========================================================================= *)

(* CURRENT (void_gates.v, void_probability_minimal.v):
   mul_fin_b, mult_fin_heat — used for:
     a) FinProb comparison: a/b <= c/d iff a*d <= c*b
     b) FinProb addition: a/b + c/d = (a*d + c*b) / (b*d)
     c) Gate operations: AND = p1 * p2
   
   Cost: O(n*m) ticks. With den=10, comparing two probs costs
   ~100 ticks minimum. This is why cells died so fast in early
   Python experiments.
   
   With Fin weights (no fractions), comparison is le_fin_b3
   which costs O(min(n,m)) ticks. Addition is add_fin which
   costs O(m) ticks. No multiplication needed.
   
   FIX: Remove multiplication from neural cell operations.
        Gates (AND/OR/XOR) are a separate concern — they operate
        on probabilities and may keep FinProb. But cells don't.
*)


(* ========================================================================= *)
(* ERROR 7: NO PREDICTIVE PROCESSING MODEL                                   *)
(* ========================================================================= *)

(* CURRENT: reactive model
     1. Receive input
     2. Compute output
     3. Compare output to truth (external label)
     4. Adjust weights based on error
   
   SHOULD BE: predictive processing (Friston/Clark)
     1. Cell has internal model (weights encode predictions)
     2. Receive input → cell PREDICTS outcome
     3. Compare prediction to truth → PREDICTION ERROR = surprise
     4. Surprise COSTS budget (free energy)
     5. Low surprise = good model = survives
     6. High surprise = bad model = dies
     7. Budget IS free energy. Heat IS entropy.
   
   The key difference: weights are FIXED at initialization.
   "Learning" is not weight adjustment — it's SELECTION.
   Bad models die. Good models survive and vote.
   This IS how the immune system works.
   This IS how evolution works.
   This is what Friston calls "active inference" at population level.
   
   Python proved: 16 cells with fixed weights, pure budget selection,
   produced 8 survivors with correct quality ordering:
     balanced > broad > decline > GOOD > BEST > [WEAK dead] > [NOISE dead]
*)


(* ========================================================================= *)
(* ERROR 8: CONSERVATION LAW INCOMPLETE                                      *)
(* ========================================================================= *)

(* CURRENT: budget + heat = initial is stated but refund breaks it.
   
   If we add refund (correct prediction gains budget), then:
     budget + heat ≠ initial
   
   Because refund comes from OUTSIDE the cell — from the environment
   (training signal). This is thermodynamically correct: an open system
   can receive free energy from its environment.
   
   But we need to track it:
     budget + heat = initial + total_refunds_received - total_penalties_paid
   
   Or simpler: track net_surprise = penalties - refunds.
   Then: budget + heat + net_surprise = initial.
   
   Actually even simpler: refund and penalty are TRANSFERS.
   The training environment has its own budget pool.
   Total across all cells + environment = constant.
   
   FIX: Either:
     a) Closed cell: no refund, pure mortality, budget only drains
     b) Open cell: track environment budget pool explicitly
   Python showed (b) works better — but (a) is simpler to prove.
*)


(* ========================================================================= *)
(* SUMMARY: WHAT NEEDS TO HAPPEN                                             *)
(* ========================================================================= *)

(*
   NEW FILE: void_predictive_cell.v
   
   Imports: void_finite_minimal (Fin, Bool3, le_fin_b3, add_fin_b_heat)
   
   DEFINES:
     1. PredictiveCell with weights_for, weights_against (list Fin),
        budget, heat (all Fin, no FinProb anywhere)
     
     2. accumulate: sum Fin weights where Bool3 inputs match
        - BTrue inputs → accumulate with weights_for
        - BFalse inputs → accumulate with weights_against  
        - BUnknown → skip both (honest ignorance)
     
     3. predict: dual-accumulator comparison via le_fin_b3
        - Both directions to detect ties
        - Tie → BUnknown (honest)
        
     4. update: prediction error → budget change
        - Match → refund (precision gain)
        - Mismatch → penalty (surprise cost)
        - Unknown → no change
   
   PROVES:
     T1. BFalse_is_active: 
         Changing one input from BUnknown to BFalse changes the prediction
         (BFalse contributes to acc_against, BUnknown does not)
     
     T2. conservation_closed:
         For cells without refund: budget + heat = initial always
     
     T3. correct_gains_budget:
         After a correct prediction with refund, budget increases
     
     T4. wrong_loses_budget:  
         After a wrong prediction, budget strictly decreases
     
     T5. tie_is_unknown:
         When acc_for = acc_against, prediction = BUnknown
     
     T6. no_evidence_is_unknown:
         All BUnknown inputs → prediction = BUnknown
     
     T7. selection_monotone:
         Cell with more correct predictions has more budget
         (= Friston's free energy principle as a theorem)
   
   DOES NOT USE:
     - FinProb (no fractions)
     - sub_fin (no subtraction, except internal budget transfer)
     - mult_fin (no multiplication)
     - erode / constrict (no weight adjustment)
     - threshold (no single-accumulator model)
   
   EXISTING FILES: untouched. New file only. Prove the new model
   is correct, then decide what to deprecate.
*)
