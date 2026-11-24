import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L7
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L8
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# `PartIII-b:C/grad/3/4/1/2/1/12`: the kernel leaf for `𝒦` on `GCombo`s (`GKopProp`)

Source `the November 2 reference manuscript`
5036-5039 (`𝒦 = η∂_η + 2s∂_s`), 5063-5079.

Proof.  Near `σ`, `F` equals `GSum e` (all `y`), a finite sum over `p = (r,a,b)` of
`c_p(t) · gEval (e p) t`, with `c_p = gCoef Ay r`.  `𝒦` is a derivation-type operator:
`𝒦 (c · g) = c · 𝒦 g + 2 (s c') g`, and `s c_0' = c_1`, `s c_1' = c_2` (`GCoefProp`).  Level `2`
terms vanish when `GLevel 1 e`.  So the new expression at level `r` is
`K0 (e r a b) ++ 2 · e (r-1) a b`, where `K0` is the kernel expression of `𝒦` (`GKerKopProp`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `p`-th term of `GSum`: `(s∂_s)^r A_{ab}(t)` times the kernel expression `e r a b`. -/
def gkT (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3)
    (p : Fin 3 × Fin 2 × Fin 2) (t : ℝ) (z : ℝ × ℝ) : ℝ :=
  gCoef Ay p.1 t (mi p.2.1) (mi p.2.2) * gEval (e p.1 p.2.1 p.2.2) ν j t z

lemma gSum_eq_gkT (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3)
    (t : ℝ) (z : ℝ × ℝ) :
    GSum e ν j Ay t z = ∑ p : Fin 3 × Fin 2 × Fin 2, gkT e ν j Ay p t z := by
  simp only [GSum, gkT, Fintype.sum_prod_type]

lemma kop_congr_gen (F G : ℝ → ℝ × ℝ → ℝ) (σ : ℝ) (y : ℝ × ℝ)
    (h : ∀ᶠ t in 𝓝 σ, ∀ z, F t z = G t z) : Kop F σ y = Kop G σ y := by
  have hF : F σ = G σ := funext (Filter.Eventually.self_of_nhds h)
  have hd : deriv (fun t => F t y) σ = deriv (fun t => G t y) σ :=
    Filter.EventuallyEq.deriv_eq (f₁ := fun t => F t y) (f := fun t => G t y)
      (h.mono fun t ht => ht y)
  unfold Kop
  rw [hF, hd]

lemma kop_mul_gen (c : ℝ → ℝ) (c' : ℝ) (g : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (y : ℝ × ℝ)
    (hc : HasDerivAt c c' s) (hg : DifferentiableAt ℝ (g s) y)
    (hgt : DifferentiableAt ℝ (fun t => g t y) s) :
    Kop (fun t z => c t * g t z) s y = c s * Kop g s y + 2 * (s * c') * g s y := by
  have h1 : fderiv ℝ (fun z => c s * g s z) y = c s • fderiv ℝ (g s) y :=
    fderiv_const_mul hg (c s)
  have h2 : deriv (fun t => c t * g t y) s = c' * g s y + c s * deriv (fun t => g t y) s :=
    (hc.mul hgt.hasDerivAt).deriv
  unfold Kop
  simp only [h1, h2, smul_apply, smul_eq_mul]
  ring

lemma kop_sum_gen {ι : Type*} (u : Finset ι) (A : ι → ℝ → ℝ × ℝ → ℝ) (s : ℝ) (y : ℝ × ℝ)
    (h : ∀ i ∈ u, DifferentiableAt ℝ (A i s) y ∧ DifferentiableAt ℝ (fun t => A i t y) s) :
    Kop (fun t z => ∑ i ∈ u, A i t z) s y = ∑ i ∈ u, Kop (A i) s y := by
  have h1 : fderiv ℝ (fun z => ∑ i ∈ u, A i s z) y = ∑ i ∈ u, fderiv ℝ (A i s) y :=
    fderiv_fun_sum (fun i hi => (h i hi).1)
  have h2 : deriv (fun t => ∑ i ∈ u, A i t y) s = ∑ i ∈ u, deriv (fun t => A i t y) s :=
    deriv_fun_sum (fun i hi => (h i hi).2)
  unfold Kop
  rw [h1, h2, _root_.sum_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

lemma kop_coef_term (K0 : GExpr → GExpr)
    (hK0 : ∀ (w : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
      Kop (gEval w ν j) s x = gEval (K0 w) ν j s x)
    (w : GExpr) (c : ℝ → ℝ) (c' : ℝ) (ν : ℝ) (j : ℤ) (s : ℝ) (y : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) (hc : HasDerivAt c c' s) :
    Kop (fun t z => c t * gEval w ν j t z) s y
      = c s * gEval (K0 w) ν j s y + 2 * (s * c') * gEval w ν j s y := by
  obtain ⟨_, hE⟩ := gKerDetaProp w
  obtain ⟨_, hS⟩ := gKerSProp w
  have hg : DifferentiableAt ℝ (gEval w ν j s) y := (hE ν j s y hν hs).1
  have hgt : DifferentiableAt ℝ (fun t => gEval w ν j t y) s :=
    (hS ν j s y hν hs).differentiableAt
  rw [kop_mul_gen c c' (gEval w ν j) s y hc hg hgt, hK0 w ν j s y hν hs]

lemma gCoef_zero_hasDeriv (Ay : ℝ → Mat3) (σ : ℝ) (hσ : 0 < σ) (hA : ContDiffAt ℝ 2 Ay σ)
    (i j : Fin 3) :
    HasDerivAt (fun t => gCoef Ay 0 t i j) (sDeriv Ay σ i j / σ) σ :=
  (gCoefProp Ay σ hσ hA i j).1

lemma gCoef_one_hasDeriv (Ay : ℝ → Mat3) (σ : ℝ) (hσ : 0 < σ) (hA : ContDiffAt ℝ 2 Ay σ)
    (i j : Fin 3) :
    HasDerivAt (fun t => gCoef Ay 1 t i j) (sDeriv (sDeriv Ay) σ i j / σ) σ :=
  (gCoefProp Ay σ hσ hA i j).2

lemma gkT_ok (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3)
    (σ : ℝ) (y : ℝ × ℝ) (hν : 0 < ν) (hσ : 0 < σ) (hA : ContDiffAt ℝ 2 Ay σ)
    (hL : ∀ r : Fin 3, 1 < r.val → ∀ a b, e r a b = []) (p : Fin 3 × Fin 2 × Fin 2) :
    DifferentiableAt ℝ (gkT e ν j Ay p σ) y ∧
      DifferentiableAt ℝ (fun t => gkT e ν j Ay p t y) σ := by
  obtain ⟨r, a, b⟩ := p
  have hr3 : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
  rcases hr3 r with rfl | rfl | rfl
  · obtain ⟨_, hE⟩ := gKerDetaProp (e 0 a b)
    obtain ⟨_, hS⟩ := gKerSProp (e 0 a b)
    have hc := gCoef_zero_hasDeriv Ay σ hσ hA (mi a) (mi b)
    refine ⟨?_, ?_⟩
    · show DifferentiableAt ℝ
        (fun z => gCoef Ay 0 σ (mi a) (mi b) * gEval (e 0 a b) ν j σ z) y
      exact ((hE ν j σ y hν hσ).1).const_mul (gCoef Ay 0 σ (mi a) (mi b))
    · show DifferentiableAt ℝ
        (fun t => gCoef Ay 0 t (mi a) (mi b) * gEval (e 0 a b) ν j t y) σ
      exact hc.differentiableAt.mul (hS ν j σ y hν hσ).differentiableAt
  · obtain ⟨_, hE⟩ := gKerDetaProp (e 1 a b)
    obtain ⟨_, hS⟩ := gKerSProp (e 1 a b)
    have hc := gCoef_one_hasDeriv Ay σ hσ hA (mi a) (mi b)
    refine ⟨?_, ?_⟩
    · show DifferentiableAt ℝ
        (fun z => gCoef Ay 1 σ (mi a) (mi b) * gEval (e 1 a b) ν j σ z) y
      exact ((hE ν j σ y hν hσ).1).const_mul (gCoef Ay 1 σ (mi a) (mi b))
    · show DifferentiableAt ℝ
        (fun t => gCoef Ay 1 t (mi a) (mi b) * gEval (e 1 a b) ν j t y) σ
      exact hc.differentiableAt.mul (hS ν j σ y hν hσ).differentiableAt
  · have h2 : e 2 a b = [] := hL 2 (by show 1 < 2; omega) a b
    have hz : ∀ t z, gkT e ν j Ay (2, a, b) t z = 0 := fun t z => by
      simp [gkT, h2, kD_gEval_nil]
    have hf : gkT e ν j Ay (2, a, b) σ = fun _ => 0 := funext fun z => hz σ z
    have hg : (fun t => gkT e ν j Ay (2, a, b) t y) = fun _ => 0 := funext fun t => hz t y
    rw [hf, hg]
    exact ⟨differentiableAt_const _, differentiableAt_const _⟩

lemma kop_gkT0 (K0 : GExpr → GExpr)
    (hK0 : ∀ (w : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
      Kop (gEval w ν j) s x = gEval (K0 w) ν j s x)
    (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3) (σ : ℝ) (y : ℝ × ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (hA : ContDiffAt ℝ 2 Ay σ) (a b : Fin 2) :
    Kop (gkT e ν j Ay (0, a, b)) σ y =
      gCoef Ay 0 σ (mi a) (mi b) * gEval (K0 (e 0 a b)) ν j σ y
        + 2 * gCoef Ay 1 σ (mi a) (mi b) * gEval (e 0 a b) ν j σ y := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hc := gCoef_zero_hasDeriv Ay σ hσ hA (mi a) (mi b)
  have hsd : σ * (sDeriv Ay σ (mi a) (mi b) / σ) = gCoef Ay 1 σ (mi a) (mi b) := by
    show σ * (sDeriv Ay σ (mi a) (mi b) / σ) = sDeriv Ay σ (mi a) (mi b)
    field_simp
  have hT := kop_coef_term K0 hK0 (e 0 a b) (fun t => gCoef Ay 0 t (mi a) (mi b))
    (sDeriv Ay σ (mi a) (mi b) / σ) ν j σ y hν hσ hc
  have hgk : gkT e ν j Ay (0, a, b)
      = fun t z => gCoef Ay 0 t (mi a) (mi b) * gEval (e 0 a b) ν j t z := rfl
  rw [hgk, hT, hsd]

lemma kop_gkT1 (K0 : GExpr → GExpr)
    (hK0 : ∀ (w : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
      Kop (gEval w ν j) s x = gEval (K0 w) ν j s x)
    (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3) (σ : ℝ) (y : ℝ × ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (hA : ContDiffAt ℝ 2 Ay σ) (a b : Fin 2) :
    Kop (gkT e ν j Ay (1, a, b)) σ y =
      gCoef Ay 1 σ (mi a) (mi b) * gEval (K0 (e 1 a b)) ν j σ y
        + 2 * gCoef Ay 2 σ (mi a) (mi b) * gEval (e 1 a b) ν j σ y := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hc := gCoef_one_hasDeriv Ay σ hσ hA (mi a) (mi b)
  have hsd : σ * (sDeriv (sDeriv Ay) σ (mi a) (mi b) / σ) = gCoef Ay 2 σ (mi a) (mi b) := by
    show σ * (sDeriv (sDeriv Ay) σ (mi a) (mi b) / σ) = sDeriv (sDeriv Ay) σ (mi a) (mi b)
    field_simp
  have hT := kop_coef_term K0 hK0 (e 1 a b) (fun t => gCoef Ay 1 t (mi a) (mi b))
    (sDeriv (sDeriv Ay) σ (mi a) (mi b) / σ) ν j σ y hν hσ hc
  have hgk : gkT e ν j Ay (1, a, b)
      = fun t z => gCoef Ay 1 t (mi a) (mi b) * gEval (e 1 a b) ν j t z := rfl
  rw [hgk, hT, hsd]

lemma kop_gkT2 (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3)
    (σ : ℝ) (y : ℝ × ℝ) (hL2 : ∀ a b, e 2 a b = []) (a b : Fin 2) :
    Kop (gkT e ν j Ay (2, a, b)) σ y = 0 := by
  have hz : ∀ t z, gkT e ν j Ay (2, a, b) t z = 0 := fun t z => by
    simp [gkT, hL2 a b, kD_gEval_nil]
  have hf : gkT e ν j Ay (2, a, b) = fun _ _ => 0 := funext fun t => funext fun z => hz t z
  rw [hf]
  simp [Kop]

theorem gKopProp : GKopProp := by
  intro L hL e he
  have hKK : ∀ w : GExpr, ∃ w' : GExpr, ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
      0 < ν → 0 < s → Kop (gEval w ν j) s x = gEval w' ν j s x := gKerKopProp
  choose K hK using hKK
  obtain ⟨K0, hK0nil, hK0⟩ : ∃ K0 : GExpr → GExpr, K0 [] = [] ∧
      ∀ (w : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
        Kop (gEval w ν j) s x = gEval (K0 w) ν j s x := by
    refine ⟨fun w => match w with | [] => [] | t :: r => K (t :: r), rfl, ?_⟩
    intro w ν j s x hν hs
    cases w with
    | nil =>
      have h0 : gEval [] ν j = fun _ _ => 0 :=
        funext fun s' => funext fun x' => kD_gEval_nil ν j s' x'
      show Kop (gEval [] ν j) s x = gEval [] ν j s x
      rw [h0]
      simp [Kop]
    | cons t r => exact hK (t :: r) ν j s x hν hs
  have hL1 : ∀ r : Fin 3, 1 < r.val → ∀ a b, e r a b = [] :=
    fun r hr a b => he r (lt_of_le_of_lt hL hr) a b
  have hL2 : ∀ a b, e 2 a b = [] := fun a b => hL1 2 (by show 1 < 2; omega) a b
  obtain ⟨E', hE0, hE1, hE2⟩ : ∃ E' : Fin 3 → Fin 2 → Fin 2 → GExpr,
      (∀ a b, E' 0 a b = K0 (e 0 a b)) ∧
      (∀ a b, E' 1 a b = K0 (e 1 a b) ++ kK_scale2 (e 0 a b)) ∧
      (∀ a b, E' 2 a b = K0 (e 2 a b) ++ kK_scale2 (e 1 a b)) :=
    ⟨fun r a b => ![K0 (e 0 a b), K0 (e 1 a b) ++ kK_scale2 (e 0 a b),
        K0 (e 2 a b) ++ kK_scale2 (e 1 a b)] r,
      fun a b => rfl, fun a b => rfl, fun a b => rfl⟩
  refine ⟨E', ?_, ?_⟩
  · intro r hr a b
    have hr3 : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
    rcases hr3 r with rfl | rfl | rfl
    · exact absurd hr (by show ¬ (L + 1 < 0); omega)
    · exact absurd hr (by show ¬ (L + 1 < 1); omega)
    · have h1 : e 1 a b = [] := he 1 (by show L < 1; omega) a b
      simp [hE2, hL2 a b, h1, hK0nil, kK_scale2]
  · intro ν j Ay s F hν hs hA hF
    unfold GCombo at hF ⊢
    have key : ∀ σ : ℝ, 0 < σ → ContDiffAt ℝ 2 Ay σ →
        (∀ᶠ t in 𝓝 σ, ∀ z, F t z = GSum e ν j Ay t z) →
        ∀ y, Kop F σ y = GSum E' ν j Ay σ y := by
      intro σ hσ hAσ hPσ y
      have hK1 : Kop F σ y
          = Kop (fun t z => ∑ p : Fin 3 × Fin 2 × Fin 2, gkT e ν j Ay p t z) σ y :=
        kop_congr_gen _ _ σ y (hPσ.mono fun t ht z => (ht z).trans (gSum_eq_gkT _ _ _ _ _ _))
      have hS := kop_sum_gen (Finset.univ : Finset (Fin 3 × Fin 2 × Fin 2))
        (fun p => gkT e ν j Ay p) σ y
        (fun p _ => gkT_ok e ν j Ay σ y hν hσ hAσ hL1 p)
      rw [hK1, hS]
      simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, GSum, hE0, hE1,
        hE2]
      simp only [kop_gkT0 K0 hK0 e ν j Ay σ y hν hσ hAσ, kop_gkT1 K0 hK0 e ν j Ay σ y hν hσ hAσ,
        kop_gkT2 e ν j Ay σ y hL2]
      simp only [hL2, hK0nil, kD_gEval_nil, kD_gEval_append, kK_scale2_eq]
      ring
    have hpos : ∀ᶠ s' in 𝓝 s, 0 < s' := eventually_gt_nhds hs
    have hC : ∀ᶠ s' in 𝓝 s, ContDiffAt ℝ 2 Ay s' := hA.eventually (by simp)
    have hF2 : ∀ᶠ s' in 𝓝 s, ∀ᶠ t in 𝓝 s', ∀ z, F t z = GSum e ν j Ay t z :=
      hF.eventually_nhds
    filter_upwards [hpos, hC, hF2] with σ hσ hAσ hPσ
    exact key σ hσ hAσ hPσ

end UnforcedLeray.Short.PartIIIb.Concrete
