import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp.Core

/-!
# All-order Leibniz expansion and integration by parts (`PartII-b:S2/1/4`, helper)

Source of record: `the November 2 reference manuscript`,
lines 2552-2559 ("In each order-`(k+1)` derivative of `w·∇w`, one factor has order at most `k`").

Words of spatial derivatives are lists `l : List (Fin 3)`, the head applied first.
* `lb f h l` is the Leibniz expansion of `D^l (f h)` for families `f h` indexed by words
  (`f a = D^a f`), defined by `D^{j :: l}(f h) = D^l (D_j f · h + f · D_j h)`.
* `iterDyL l Φ = ∂_{l₀} ∂_{l₁} ⋯ Φ` on tests, with `iterDy β Φ = iterDyL (List.ofFn β) Φ`.
* `ibp_lb`: moving all derivatives of `iterDyL l ψ` onto `f [] · h []` with `weakMulRule`
  (one weak product rule per step) gives `(-1)^{|l|} ⟪ψ, lb f h l⟫`.
* `lb_closure`: any additive property of all products `f a · h b`, `|a| + |b| = |l|`,
  passes to `lb f h l`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

namespace IterQuadSub

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Cons.C03.Concrete (phaseInt phaseCell pairF advT)
open scoped ContDiff

/-- Leibniz expansion of `D^l (f h)` (head of `l` applied first). -/
def lb : (List (Fin 3) → ℝ × UnforcedLeray.Space → ℂ) →
    (List (Fin 3) → ℝ × UnforcedLeray.Space → ℂ) → List (Fin 3) →
    ℝ × UnforcedLeray.Space → ℂ
  | f, h, [] => fun x => f [] x * h [] x
  | f, h, j :: l => fun x =>
      lb (fun a => f (j :: a)) h l x + lb f (fun b => h (j :: b)) l x

/-- Iterated spatial derivative along a word: `iterDyL (j :: l) Φ = ∂_j (iterDyL l Φ)`. -/
def iterDyL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    List (Fin 3) → (ℝ × UnforcedLeray.Space → F) → ℝ × UnforcedLeray.Space → F
  | [], Φ => Φ
  | j :: l, Φ => dy j (iterDyL l Φ)

theorem isPhaseTest_iterDyL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {P : ℝ} :
    ∀ (l : List (Fin 3)) {Φ : ℝ × UnforcedLeray.Space → F},
      IsPhaseTest P Φ → IsPhaseTest P (iterDyL l Φ)
  | [], _, hΦ => hΦ
  | j :: l, _, hΦ => (isPhaseTest_iterDyL l hΦ).dy j

theorem contDiff_iterDyL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∀ (l : List (Fin 3)) {Φ : ℝ × UnforcedLeray.Space → F},
      ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ (iterDyL l Φ)
  | [], _, hΦ => hΦ
  | j :: l, _, hΦ => contDiff_dyT (contDiff_iterDyL l hΦ) j

theorem iterDyL_append {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∀ (l : List (Fin 3)) (j : Fin 3) (Φ : ℝ × UnforcedLeray.Space → F),
      iterDyL (l ++ [j]) Φ = iterDyL l (dy j Φ)
  | [], _, _ => rfl
  | a :: l, j, Φ => by
      show dy a (iterDyL (l ++ [j]) Φ) = dy a (iterDyL l (dy j Φ))
      rw [iterDyL_append l j Φ]

theorem ofFn_succ_eq {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) :
    List.ofFn f = List.ofFn (Fin.init f) ++ [f (Fin.last n)] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

theorem iterDy_eq_iterDyL :
    ∀ {k : ℕ} (β : Fin k → Fin 3) (Φ : ℝ × UnforcedLeray.Space → CVec3),
      iterDy β Φ = iterDyL (List.ofFn β) Φ
  | 0, β, Φ => by simp [iterDy, iterDyL]
  | k + 1, β, Φ => by
      show iterDy (Fin.init β) (dy (β (Fin.last k)) Φ) = _
      rw [iterDy_eq_iterDyL (Fin.init β), ofFn_succ_eq β, iterDyL_append]

theorem iterDyL_comp_coord :
    ∀ (l : List (Fin 3)) {Φ : ℝ × UnforcedLeray.Space → CVec3}, ContDiff ℝ ∞ Φ →
      ∀ i : Fin 3, (fun x => iterDyL l Φ x i) = iterDyL l (fun x => Φ x i)
  | [], _, _, _ => rfl
  | j :: l, Φ, hΦ, i => by
      funext x
      show dy j (iterDyL l Φ) x i = dy j (iterDyL l (fun x => Φ x i)) x
      rw [← iterDyL_comp_coord l hΦ i]
      exact (dy_comp_coord (contDiff_iterDyL l hΦ) j i x).symm

/-- Additive properties of all products pass to the Leibniz expansion. -/
theorem lb_closure (Q : (ℝ × UnforcedLeray.Space → ℂ) → Prop)
    (hQ : ∀ F G, Q F → Q G → Q (fun x => F x + G x)) :
    ∀ (l : List (Fin 3)) (f h : List (Fin 3) → ℝ × UnforcedLeray.Space → ℂ),
      (∀ a b : List (Fin 3), a.length + b.length = l.length → Q (fun x => f a x * h b x)) →
      Q (lb f h l)
  | [], f, h, H => H [] [] rfl
  | j :: l, f, h, H =>
      hQ _ _
        (lb_closure Q hQ l (fun a => f (j :: a)) h fun a b hab =>
          H (j :: a) b (by simp only [List.length_cons] at hab ⊢; omega))
        (lb_closure Q hQ l f (fun b => h (j :: b)) fun a b hab =>
          H a (j :: b) (by simp only [List.length_cons] at hab ⊢; omega))

/-- **All-order integration by parts** (source 2552-2559): moving the derivatives of
`iterDyL l ψ` onto `f [] · h []` one at a time with `weakMulRule`. -/
theorem ibp_lb {P : ℝ} [Fact (0 < P)] :
    ∀ (l : List (Fin 3)) (f h : List (Fin 3) → ℝ × UnforcedLeray.Space → ℂ),
      (∀ a : List (Fin 3), a.length < l.length → ∀ j, WeakDyS P j (f a) (f (a ++ [j]))) →
      (∀ a : List (Fin 3), a.length < l.length → ∀ j, WeakDyS P j (h a) (h (a ++ [j]))) →
      (∀ a : List (Fin 3), a.length < l.length →
        MemLpLoc P (f a) (2 * UnforcedLeray.B0412.q0E)) →
      (∀ a : List (Fin 3), a.length < l.length →
        MemLpLoc P (h a) (2 * UnforcedLeray.B0412.q0E)) →
      (∀ a : List (Fin 3), a.length ≤ l.length → MemLpLoc P (f a) UnforcedLeray.B0412.q0E) →
      (∀ a : List (Fin 3), a.length ≤ l.length → MemLpLoc P (h a) UnforcedLeray.B0412.q0E) →
      ∀ ψ : ℝ × UnforcedLeray.Space → ℂ, IsPhaseTest P ψ →
        phaseInt P (fun x => iterDyL l ψ x * (f [] x * h [] x)) =
          (-1) ^ l.length * phaseInt P (fun x => ψ x * lb f h l x)
  | [], f, h, _, _, _, _, _, _, ψ, _ => by
      simp only [iterDyL, lb, List.length_nil, pow_zero, one_mul]
  | j :: l, f, h, hWf, hWh, hf2, hh2, hfq, hhq, ψ, hψ => by
      have hθ : IsPhaseTest P (iterDyL l ψ) := isPhaseTest_iterDyL l hψ
      have h0 : ([] : List (Fin 3)).length < (j :: l).length := by simp
      have h1 : [j].length ≤ (j :: l).length := by simp
      have hW := (weakMulRule : WeakMulRule) P j (f []) (h []) (f [j]) (h [j])
        (hf2 [] h0) (hh2 [] h0) (hfq [j] h1) (hhq [j] h1) (hWf [] h0 j) (hWh [] h0 j)
      have step1 : phaseInt P (fun x => iterDyL (j :: l) ψ x * (f [] x * h [] x)) =
          -phaseInt P (fun x => iterDyL l ψ x * (f [j] x * h [] x + f [] x * h [j] x)) :=
        hW _ hθ
      have L2f : ∀ a : List (Fin 3), a.length ≤ (j :: l).length → MemLpLoc P (f a) 2 :=
        fun a ha => memLpLoc_mono (hfq a ha) q0E_two_le
      have L2h : ∀ a : List (Fin 3), a.length ≤ (j :: l).length → MemLpLoc P (h a) 2 :=
        fun a ha => memLpLoc_mono (hhq a ha) q0E_two_le
      have I1 : Integrable (fun x => iterDyL l ψ x * (f [j] x * h [] x))
          (volume.restrict (phaseCell P)) :=
        integrable_test_mul2 hθ (L2f [j] h1) (L2h [] (by simp))
      have I2 : Integrable (fun x => iterDyL l ψ x * (f [] x * h [j] x))
          (volume.restrict (phaseCell P)) :=
        integrable_test_mul2 hθ (L2f [] (by simp)) (L2h [j] h1)
      have split : phaseInt P (fun x => iterDyL l ψ x * (f [j] x * h [] x + f [] x * h [j] x)) =
          phaseInt P (fun x => iterDyL l ψ x * (f [j] x * h [] x)) +
            phaseInt P (fun x => iterDyL l ψ x * (f [] x * h [j] x)) := by
        rw [← phaseInt_add_cell I1 I2]
        congr 1
        funext x
        ring
      have e1 := ibp_lb l (fun a => f (j :: a)) h
        (fun a ha j' => hWf (j :: a) (by simp only [List.length_cons]; omega) j')
        (fun a ha j' => hWh a (by simp only [List.length_cons]; omega) j')
        (fun a ha => hf2 (j :: a) (by simp only [List.length_cons]; omega))
        (fun a ha => hh2 a (by simp only [List.length_cons]; omega))
        (fun a ha => hfq (j :: a) (by simp only [List.length_cons]; omega))
        (fun a ha => hhq a (by simp only [List.length_cons]; omega)) ψ hψ
      have e2 := ibp_lb l f (fun b => h (j :: b))
        (fun a ha j' => hWf a (by simp only [List.length_cons]; omega) j')
        (fun a ha j' => hWh (j :: a) (by simp only [List.length_cons]; omega) j')
        (fun a ha => hf2 a (by simp only [List.length_cons]; omega))
        (fun a ha => hh2 (j :: a) (by simp only [List.length_cons]; omega))
        (fun a ha => hfq a (by simp only [List.length_cons]; omega))
        (fun a ha => hhq (j :: a) (by simp only [List.length_cons]; omega)) ψ hψ
      have hQ : ∀ F G : ℝ × UnforcedLeray.Space → ℂ,
          Integrable (fun x => ψ x * F x) (volume.restrict (phaseCell P)) →
          Integrable (fun x => ψ x * G x) (volume.restrict (phaseCell P)) →
          Integrable (fun x => ψ x * (F x + G x)) (volume.restrict (phaseCell P)) := by
        intro F G hF hG
        refine (hF.add hG).congr (ae_of_all _ fun x => ?_)
        simp only [Pi.add_apply]
        ring
      have J1 : Integrable (fun x => ψ x * lb (fun a => f (j :: a)) h l x)
          (volume.restrict (phaseCell P)) :=
        lb_closure (fun F => Integrable (fun x => ψ x * F x) (volume.restrict (phaseCell P)))
          hQ l _ _ fun a b hab =>
            integrable_test_mul2 hψ (L2f (j :: a) (by simp only [List.length_cons]; omega))
              (L2h b (by simp only [List.length_cons]; omega))
      have J2 : Integrable (fun x => ψ x * lb f (fun b => h (j :: b)) l x)
          (volume.restrict (phaseCell P)) :=
        lb_closure (fun F => Integrable (fun x => ψ x * F x) (volume.restrict (phaseCell P)))
          hQ l _ _ fun a b hab =>
            integrable_test_mul2 hψ (L2f a (by simp only [List.length_cons]; omega))
              (L2h (j :: b) (by simp only [List.length_cons]; omega))
      have hR : phaseInt P (fun x => ψ x * lb f h (j :: l) x) =
          phaseInt P (fun x => ψ x * lb (fun a => f (j :: a)) h l x) +
            phaseInt P (fun x => ψ x * lb f (fun b => h (j :: b)) l x) := by
        rw [← phaseInt_add_cell J1 J2]
        congr 1
        funext x
        show ψ x * (lb (fun a => f (j :: a)) h l x + lb f (fun b => h (j :: b)) l x) = _
        ring
      have e1' : phaseInt P (fun x => iterDyL l ψ x * (f [j] x * h [] x)) =
          (-1) ^ l.length * phaseInt P (fun x => ψ x * lb (fun a => f (j :: a)) h l x) := e1
      have e2' : phaseInt P (fun x => iterDyL l ψ x * (f [] x * h [j] x)) =
          (-1) ^ l.length * phaseInt P (fun x => ψ x * lb f (fun b => h (j :: b)) l x) := e2
      rw [step1, split, e1', e2', hR, List.length_cons, pow_succ]
      ring

end IterQuadSub

end UnforcedLeray.Short.IIb
