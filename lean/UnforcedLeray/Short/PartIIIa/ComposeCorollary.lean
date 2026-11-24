import UnforcedLeray.Short.PartIIIa.FlatCausal
import UnforcedLeray.Short.PartIIIa.FlatCausalMeas

/-!
# Part III-a: `cor:short-polynomial-stress` from `prop:short-polynomial-causal`

SP 3560-3581. The proof follows the source: `b = S_lin(F₁+F₂)` solves the free equation with
tensor `(F₁ - M₀b) + F₂` (algebraic reduction of the weak equation), and the bound is the sum of
the proposition's bound for `b` with the multiplier bound and `‖F₁+F₂‖_𝒯 ≤ ‖F‖_𝒵`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Euclidean model of `tnorm2` -/

/-- A `2×2` complex tensor as a vector of `EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
def toE (T : Fin 2 → Fin 2 → ℂ) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun k => T k.1 k.2)

theorem tnorm2_eq (T : Fin 2 → Fin 2 → ℂ) : tnorm2 T = ‖toE T‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [tnorm2, toE, Fintype.sum_prod_type]

theorem tnorm2_sub_le (T S : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => T i j - S i j) ≤ tnorm2 T + tnorm2 S := by
  rw [tnorm2_eq, tnorm2_eq, tnorm2_eq]
  have : toE (fun i j => T i j - S i j) = toE T - toE S := by ext k; simp [toE]
  rw [this]
  exact norm_sub_le _ _

theorem tnorm2_add_le (T S : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => T i j + S i j) ≤ tnorm2 T + tnorm2 S := by
  rw [tnorm2_eq, tnorm2_eq, tnorm2_eq]
  have : toE (fun i j => T i j + S i j) = toE T + toE S := by ext k; simp [toE]
  rw [this]
  exact norm_add_le _ _

theorem tnorm2_nonneg (T : Fin 2 → Fin 2 → ℂ) : 0 ≤ tnorm2 T := Real.sqrt_nonneg _

-- `measurable_tnorm2` and `measurable_gainConj_vec` are in `FlatCausalMeas.lean`.

/-- Triangle inequality in `L²` for a pointwise bound `|h| ≤ f + g`. -/
theorem eLpNorm_two_le_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh : ∀ x, ‖h x‖ ≤ f x + g x) :
    eLpNorm h 2 μ ≤ eLpNorm f 2 μ + eLpNorm g 2 μ := by
  calc eLpNorm h 2 μ ≤ eLpNorm (f + g) 2 μ := by
        refine eLpNorm_mono fun x => ?_
        simpa [Real.norm_of_nonneg (add_nonneg (hf0 x) (hg0 x))] using hh x
    _ ≤ _ := eLpNorm_add_le hf hg (by norm_num)

theorem measurable_gainConj {γ ν : ℝ} {f : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hf : ∀ i j, Measurable fun p => f p i j) (i j : Fin 2) :
    Measurable fun p => gainConj γ ν f p i j := by
  have hg : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ := by
    unfold gainG; fun_prop
  exact hg.smul (hf i j)


theorem gainConj_flatMult {ν c : ℝ} (γ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    gainConj γ ν (flatMult tr u) = flatMult tr (gainConj γ ν u) := by
  funext p i j
  simp only [gainConj, flatMult, Pi.smul_apply, Complex.real_smul]
  push_cast
  ring

/-- Weighted triangle inequality for the `𝒵₁` norm of a difference. -/
theorem z1Norm2_sub_le {c mZ : ℝ} {T S : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ i j, Measurable fun p => T p i j) (hS : ∀ i j, Measurable fun p => S p i j) :
    z1Norm2 c mZ (fun p i j => T p i j - S p i j) ≤ z1Norm2 c mZ T + z1Norm2 c mZ S := by
  have hW : Measurable (transWeight mZ) := by unfold transWeight; fun_prop
  have hW0 : ∀ p, 0 ≤ transWeight mZ p := fun p => by unfold transWeight; positivity
  refine eLpNorm_two_le_add (f := fun p => transWeight mZ p * tnorm2 (T p))
    (g := fun p => transWeight mZ p * tnorm2 (S p)) ?_ ?_ (fun p => ?_) (fun p => ?_) (fun p => ?_)
  · exact (hW.mul (measurable_tnorm2 hT)).aestronglyMeasurable
  · exact (hW.mul (measurable_tnorm2 hS)).aestronglyMeasurable
  · exact mul_nonneg (hW0 p) (tnorm2_nonneg _)
  · exact mul_nonneg (hW0 p) (tnorm2_nonneg _)
  · rw [Real.norm_of_nonneg (mul_nonneg (hW0 p) (tnorm2_nonneg _)), ← mul_add]
    exact mul_le_mul_of_nonneg_left (tnorm2_sub_le _ _) (hW0 p)

theorem tCalNorm_add_le {c : ℝ} {T S : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ i j, Measurable fun p => T p i j) (hS : ∀ i j, Measurable fun p => S p i j) :
    tCalNorm c (fun p i j => T p i j + S p i j) ≤ tCalNorm c T + tCalNorm c S := by
  refine eLpNorm_two_le_add (f := fun p => tnorm2 (T p)) (g := fun p => tnorm2 (S p))
    (measurable_tnorm2 hT).aestronglyMeasurable (measurable_tnorm2 hS).aestronglyMeasurable
    (fun p => tnorm2_nonneg _) (fun p => tnorm2_nonneg _) (fun p => ?_)
  rw [Real.norm_of_nonneg (tnorm2_nonneg _)]
  exact tnorm2_add_le _ _

/-- `‖T‖_𝒯 ≤ ‖T‖_{𝒵₁}` because `W ≥ 1` (`m_Z ≥ 0`). -/
theorem tCalNorm_le_z1Norm2 {c mZ : ℝ} (hmZ : 0 ≤ mZ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNorm c T ≤ z1Norm2 c mZ T := by
  refine eLpNorm_mono fun p => ?_
  have hW : 1 ≤ transWeight mZ p := by
    unfold transWeight
    exact Real.one_le_rpow (by nlinarith [sq_nonneg (p.2.2 / Real.sqrt (1 + p.1))])
      (by positivity)
  rw [Real.norm_of_nonneg (tnorm2_nonneg _),
    Real.norm_of_nonneg (mul_nonneg (by linarith) (tnorm2_nonneg _))]
  nlinarith [tnorm2_nonneg (T p)]

/-! ## The algebraic reduction -/

theorem flatIntegrand_free_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (μ : ℂ)
    (F₁ F₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) :
    flatIntegrand ν μ (fun _ _ _ => 0)
        (fun p i j => (F₁ p i j - flatMult tr b p i j) + F₂ p i j) b Φ =
      flatIntegrand ν μ (trainVel tr) (fun p i j => F₁ p i j + F₂ p i j) b Φ := by
  funext p
  simp only [flatIntegrand, flatMult]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- `b = S_lin(F₁+F₂)` solves the free equation with tensor `(F₁ - M₀b) + F₂`. -/
theorem causal_free_reduction {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (μ : ℂ)
    {F₁ F₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (h : IsCausalEnergySolution c ν μ (trainVel tr) (fun p i j => F₁ p i j + F₂ p i j) b G) :
    IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
      (fun p i j => (F₁ p i j - flatMult tr b p i j) + F₂ p i j) b G where
  measurable := h.measurable
  gradMeasurable := h.gradMeasurable
  energyLoc := h.energyLoc
  zeroEntrance := h.zeroEntrance
  divFree := h.divFree
  weakGrad := h.weakGrad
  integrable := fun Φ hΦ => by
    rw [flatIntegrand_free_eq]; exact h.integrable Φ hΦ
  weak := fun Φ hΦ => by
    rw [flatIntegrand_free_eq]; exact h.weak Φ hΦ

/-! ## Measurability of the train coefficient -/

theorem measurable_trainVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : Fin 2) :
    Measurable fun p : ℝ × (ℝ × ℝ) => trainVel tr p.1 p.2 i := by
  have h2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) {p | 0 ≤ p.1} := by
    refine tr.isTrain.smooth_v.continuousOn.mono ?_
    intro p hp
    exact ⟨hp, mem_univ _⟩
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 i) {p | 0 ≤ p.1} :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn h2
  have hs : MeasurableSet {p : ℝ × (ℝ × ℝ) | 0 ≤ p.1} :=
    measurableSet_le measurable_const measurable_fst
  have := hcont.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hs
  convert this using 1
  ext p
  simp [trainVel, Set.piecewise]

theorem measurable_flatMult {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i) (i j : Fin 2) :
    Measurable fun p => flatMult tr u p i j := by
  have hi := (measurable_trainVel tr i).complex_ofReal
  have hj := (measurable_trainVel tr j).complex_ofReal
  unfold flatMult
  exact (hi.mul (hu j)).add ((hu i).mul hj)

/-! ## The corollary -/

/-- **`cor:short-polynomial-stress`** (SP 3560-3581) from `prop:short-polynomial-causal`. -/
theorem polyStressCorollary_of_polyCausal (hPoly : PolyCausal) : PolyStressCorollary := by
  intro P hP K hK mZ hmZ pV
  obtain ⟨M₀, C₀, ν₀', hν₀', hpc⟩ := hPoly P hP K hK
  refine ⟨pV + M₀, fun CV => ⟨1 + |CV| * |C₀|, min ν₀' 1, lt_min hν₀' one_pos, ?_⟩⟩
  intro ν hν tr htr ρb hρ hρ1 hV μ hμ F₁ F₂ hs₁ hs₂ hm₁ hm₂ hfin
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hν' : ν ∈ Ioc 0 ν₀' := ⟨hν0, hν.2.trans (min_le_left _ _)⟩
  have hg1 : ∀ i j, Measurable fun p => gainConj P.eigenvalue.re ν F₁ p i j :=
    fun i j => measurable_gainConj hm₁ i j
  have hg2 : ∀ i j, Measurable fun p => gainConj P.eigenvalue.re ν F₂ p i j :=
    fun i j => measurable_gainConj hm₂ i j
  have hsumEq : gainConj P.eigenvalue.re ν (fun p i j => F₁ p i j + F₂ p i j) =
      fun p i j => gainConj P.eigenvalue.re ν F₁ p i j + gainConj P.eigenvalue.re ν F₂ p i j := by
    funext p i j; simp [gainConj, smul_add]
  have hρ' : (1 : ℝ) ≤ ρb ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  have hsum : tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν (fun p i j => F₁ p i j + F₂ p i j)) ≤
      zNorm2 (ν ^ (-2 : ℝ)) mZ ρb (gainConj P.eigenvalue.re ν F₁) (gainConj P.eigenvalue.re ν F₂) := by
    rw [hsumEq]
    refine (tCalNorm_add_le hg1 hg2).trans ?_
    unfold zNorm2
    exact add_le_add (tCalNorm_le_z1Norm2 (by linarith) _)
      (le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 hρ'))
  obtain ⟨b, G, hsol, hbound, -⟩ := hpc ν hν' tr htr μ hμ (fun p i j => F₁ p i j + F₂ p i j)
    (fun p i j => by rw [hs₁ p i j, hs₂ p i j]) (fun i j => (hm₁ i j).add (hm₂ i j))
    (lt_of_le_of_lt hsum hfin)
  refine ⟨b, G, hsol, causal_free_reduction tr μ hsol, ?_⟩
  set Z := zNorm2 (ν ^ (-2 : ℝ)) mZ ρb (gainConj P.eigenvalue.re ν F₁) (gainConj P.eigenvalue.re ν F₂) with hZ
  have hu : ∀ i, Measurable fun p => gainConj P.eigenvalue.re ν b p i :=
    fun i => measurable_gainConj_vec hsol.measurable i
  have hVb := hV (gainConj P.eigenvalue.re ν b) hu
  have hbb : hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) ≤
      ENNReal.ofReal (C₀ * ν ^ (-(M₀ : ℝ))) * Z :=
    (le_self_add.trans hbound).trans (mul_le_mul' le_rfl hsum)
  have hS : ∀ i j, Measurable fun p => gainConj P.eigenvalue.re ν (flatMult tr b) p i j := by
    intro i j
    rw [gainConj_flatMult]
    exact measurable_flatMult tr hu i j
  have hsub : gainConj P.eigenvalue.re ν (fun p i j => F₁ p i j - flatMult tr b p i j) =
      fun p i j => gainConj P.eigenvalue.re ν F₁ p i j - gainConj P.eigenvalue.re ν (flatMult tr b) p i j := by
    funext p i j; simp [gainConj, smul_sub]
  have hMb : z1Norm2 (ν ^ (-2 : ℝ)) mZ (gainConj P.eigenvalue.re ν (flatMult tr b)) ≤
      ENNReal.ofReal (|CV| * ν ^ (-(pV : ℝ))) *
        (ENNReal.ofReal (|C₀| * ν ^ (-(M₀ : ℝ))) * Z) := by
    rw [gainConj_flatMult]
    refine hVb.trans ?_
    have hpos : ∀ r : ℝ, 0 < ν ^ r := fun r => Real.rpow_pos_of_pos hν0 r
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self _) (hpos _).le)) ?_
    refine hbb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self _) (hpos _).le)) le_rfl)
  have hmain : zNorm2 (ν ^ (-2 : ℝ)) mZ ρb (gainConj P.eigenvalue.re ν (fun p i j => F₁ p i j - flatMult tr b p i j))
      (gainConj P.eigenvalue.re ν F₂) ≤ Z + ENNReal.ofReal (|CV| * ν ^ (-(pV : ℝ))) *
        (ENNReal.ofReal (|C₀| * ν ^ (-(M₀ : ℝ))) * Z) := by
    unfold zNorm2
    rw [hsub]
    have := z1Norm2_sub_le (c := ν ^ (-2 : ℝ)) (mZ := mZ) hg1 hS
    calc _ ≤ (z1Norm2 (ν ^ (-2 : ℝ)) mZ (gainConj P.eigenvalue.re ν F₁) + z1Norm2 (ν ^ (-2 : ℝ)) mZ (gainConj P.eigenvalue.re ν (flatMult tr b))) +
          ENNReal.ofReal (ρb ^ (-1 / 2 : ℝ)) * tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F₂) :=
          add_le_add this le_rfl
      _ = Z + z1Norm2 (ν ^ (-2 : ℝ)) mZ (gainConj P.eigenvalue.re ν (flatMult tr b)) := by
          rw [hZ]; unfold zNorm2; ring
      _ ≤ _ := add_le_add le_rfl hMb
  refine hmain.trans ?_
  have hν1' : ∀ r : ℝ, 0 ≤ r → 1 ≤ ν ^ (-r) := fun r hr =>
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by linarith)
  have ha := hν1' (pV : ℝ) (by positivity)
  have ha0 := hν1' (M₀ : ℝ) (by positivity)
  have hprod : ν ^ (-((pV + M₀ : ℕ) : ℝ)) = ν ^ (-(pV : ℝ)) * ν ^ (-(M₀ : ℝ)) := by
    rw [← Real.rpow_add hν0]; congr 1; push_cast; ring
  have hab : 1 ≤ ν ^ (-(pV : ℝ)) * ν ^ (-(M₀ : ℝ)) := one_le_mul_of_one_le_of_one_le ha ha0
  have key : ENNReal.ofReal (|CV| * ν ^ (-(pV : ℝ))) *
      (ENNReal.ofReal (|C₀| * ν ^ (-(M₀ : ℝ))) * Z) =
      ENNReal.ofReal ((|CV| * ν ^ (-(pV : ℝ))) * (|C₀| * ν ^ (-(M₀ : ℝ)))) * Z := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hnn : 0 ≤ ((|CV| * ν ^ (-(pV : ℝ))) * (|C₀| * ν ^ (-(M₀ : ℝ)))) := by positivity
  calc Z + ENNReal.ofReal (|CV| * ν ^ (-(pV : ℝ))) *
        (ENNReal.ofReal (|C₀| * ν ^ (-(M₀ : ℝ))) * Z)
      = ENNReal.ofReal (1 + (|CV| * ν ^ (-(pV : ℝ))) * (|C₀| * ν ^ (-(M₀ : ℝ)))) * Z := by
        rw [key, ENNReal.ofReal_add (by norm_num) hnn, ENNReal.ofReal_one, add_mul, one_mul]
    _ ≤ ENNReal.ofReal ((1 + |CV| * |C₀|) * ν ^ (-((pV + M₀ : ℕ) : ℝ))) * Z := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [hprod]
        have hCC : 0 ≤ |CV| * |C₀| := by positivity
        nlinarith [mul_nonneg hCC (sub_nonneg.2 hab)]

end UnforcedLeray.Short.IIIa
