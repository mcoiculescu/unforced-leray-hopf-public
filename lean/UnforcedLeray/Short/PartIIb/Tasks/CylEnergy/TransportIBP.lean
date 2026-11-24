import UnforcedLeray.Short.PartIIb.Sub.T22
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Lib.Cylinder.Seam
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Part II-b, task `PartII-b:T22`, leaf 5: the transport term (`CylTransportIBP`)

Source of record: `the November 2 reference manuscript`, lines 2092-2093 and
2097-2101 (the weighted integration by parts that "transports the radial weight").

Route. Let `χ_R(η) = χ(η/R)` for a fixed bump `χ` (`χ = 1` on `[-1, 1]`, support in `(-2, 2)`).
Then `g χ_R` has compact support in `η`, and `transport_antisymm` (`Lib/Cylinder/Seam.lean`) applies
to `w := g χ_R` with the centred weight `ρ := jb^m` (its seam values agree). Expanding the
derivatives gives, with `G = g (v·∇g) ρ`, `H = g² (v·∇ρ)`, `L_R = χ χ' g² ρ v₁`,

  `∫ χ² G + ∫ L_R = -(1/2) ∫ χ² H`.

Here `|χ'| ≤ K/R`, so `|L_R| ≤ (K M / R) g² ρ` and `∫ L_R → 0`; and `χ_R → 1` pointwise, so the
other two terms converge by dominated convergence. This gives `∫ G = -(1/2) ∫ H`. Integrability of
`G` and `H` follows from the decay of `g` and its first derivatives and `∫ jb^{-4} < ∞`.
The velocity's spatial derivatives are never bounded: only `v` itself, `div v = 0` (used pointwise)
and the `C¹` regularity of `v` on each slice enter.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

namespace TransportIBP

/-! ## The cut-off in `η` -/

/-- The fixed bump: `1` on `[-1, 1]`, supported in `(-2, 2)`. -/
def cutBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem cutBump_rIn : cutBump.rIn = 1 := rfl

theorem cutBump_rOut : cutBump.rOut = 2 := rfl

/-- The cut-off `χ_R(η) = χ(η / R)`. -/
def cutF (R η : ℝ) : ℝ := cutBump (R⁻¹ * η)

/-- The `η`-derivative of `cutF R`. -/
def cutD (R η : ℝ) : ℝ := R⁻¹ * deriv (fun x : ℝ => cutBump x) (R⁻¹ * η)

theorem cutF_contDiff (R : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : ℝ => cutF R η) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : ℝ => R⁻¹ * η) :=
    contDiff_const.mul contDiff_id
  exact cutBump.contDiff.comp h

theorem cutF_nonneg (R η : ℝ) : 0 ≤ cutF R η := cutBump.nonneg

theorem cutF_le_one (R η : ℝ) : cutF R η ≤ 1 := cutBump.le_one

theorem cutF_eq_one {R η : ℝ} (hR : 0 < R) (h : |η| ≤ R) : cutF R η = 1 := by
  unfold cutF
  apply cutBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, cutBump_rIn, abs_mul,
    abs_of_pos (inv_pos.2 hR), inv_mul_le_iff₀ hR]
  linarith

theorem cutF_eq_zero {R η : ℝ} (hR : 0 < R) (h : 2 * R ≤ |η|) : cutF R η = 0 := by
  unfold cutF
  apply cutBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, cutBump_rOut, abs_mul, abs_of_pos (inv_pos.2 hR),
    le_inv_mul_iff₀ hR]
  linarith

theorem hasDerivAt_cutF (R η : ℝ) : HasDerivAt (fun x : ℝ => cutF R x) (cutD R η) η := by
  have hcb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => cutBump x) := cutBump.contDiff
  have h1 : HasDerivAt (fun x : ℝ => cutBump x)
      (deriv (fun x : ℝ => cutBump x) (R⁻¹ * η)) (R⁻¹ * η) :=
    ((hcb.differentiable (by simp)) (R⁻¹ * η)).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => R⁻¹ * x) R⁻¹ η := by
    simpa using (hasDerivAt_id η).const_mul R⁻¹
  have h3 := h1.comp η h2
  have e : cutD R η = deriv (fun x : ℝ => cutBump x) (R⁻¹ * η) * R⁻¹ := by
    unfold cutD
    ring
  rw [e]
  exact h3

theorem continuous_deriv_cutBump : Continuous (deriv (fun x : ℝ => cutBump x)) := by
  have hcb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => cutBump x) := cutBump.contDiff
  exact hcb.continuous_deriv (by exact_mod_cast le_top)

theorem continuous_cutD (R : ℝ) : Continuous fun η : ℝ => cutD R η :=
  continuous_const.mul (continuous_deriv_cutBump.comp (continuous_const.mul continuous_id))

theorem exists_cutD_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R η : ℝ, 0 < R → |cutD R η| ≤ K * (1 / R) := by
  have hcs : HasCompactSupport (deriv (fun x : ℝ => cutBump x)) :=
    cutBump.hasCompactSupport.deriv
  obtain ⟨K, hK⟩ := continuous_deriv_cutBump.bounded_above_of_compact_support hcs
  refine ⟨max K 0, le_max_right _ _, fun R η hR => ?_⟩
  have hpos : 0 < R⁻¹ := inv_pos.2 hR
  have hb : |deriv (fun x : ℝ => cutBump x) (R⁻¹ * η)| ≤ max K 0 := by
    have := hK (R⁻¹ * η)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  unfold cutD
  rw [one_div, abs_mul, abs_of_pos hpos, mul_comm (max K 0)]
  exact mul_le_mul_of_nonneg_left hb hpos.le

/-! ## Decay bounds for `g` -/

theorem decay_bound {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      |g x| * B0579.jb x ^ N ≤ C ∧ |B0579.pd 0 g x| * B0579.jb x ^ N ≤ C ∧
        |B0579.pd 1 g x| * B0579.jb x ^ N ≤ C := by
  obtain ⟨C, hC⟩ := hg.cell_decay N
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hp : 0 ≤ B0579.jb x ^ N := Real.rpow_nonneg (B0579.jb_pos x).le N
  have key : (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ N
      ≤ max C 0 := (hC x hx).trans (le_max_left C 0)
  have h0 := abs_nonneg (g x)
  have h1 := abs_nonneg (B0579.pd 0 g x)
  have h2 := abs_nonneg (B0579.pd 1 g x)
  have h3 := abs_nonneg (lapP g x)
  refine ⟨?_, ?_, ?_⟩
  · have e : |g x| * B0579.jb x ^ N ≤
        (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ N :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    exact e.trans key
  · have e : |B0579.pd 0 g x| * B0579.jb x ^ N ≤
        (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ N :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    exact e.trans key
  · have e : |B0579.pd 1 g x| * B0579.jb x ^ N ≤
        (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ N :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    exact e.trans key

theorem jb_split (x : B0579.Plane) (m : ℝ) :
    B0579.jb x ^ m = B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ ((m + 4) / 2) *
      B0579.jb x ^ (-4 : ℝ) := by
  rw [← Real.rpow_add (B0579.jb_pos x), ← Real.rpow_add (B0579.jb_pos x)]
  congr 1
  ring

theorem integrable_jb_neg4 : Integrable (fun x : B0579.Plane => B0579.jb x ^ (-4 : ℝ)) :=
  UnforcedLeray.Cyl.integrable_rpow_neg_ρc (m := 4) (by norm_num)

theorem g2rho_bound {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (m : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      |g x| * |B0579.pd 0 g x| * B0579.jb x ^ m ≤ C * C * B0579.jb x ^ (-4 : ℝ) ∧
      |g x| * |B0579.pd 1 g x| * B0579.jb x ^ m ≤ C * C * B0579.jb x ^ (-4 : ℝ) ∧
      g x ^ 2 * B0579.jb x ^ m ≤ C * C * B0579.jb x ^ (-4 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := decay_bound hg ((m + 4) / 2)
  refine ⟨C, hC0, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2⟩ := hC x hx
  have hN : 0 ≤ B0579.jb x ^ ((m + 4) / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have hQ : 0 ≤ B0579.jb x ^ (-4 : ℝ) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have e : g x ^ 2 = |g x| * |g x| := by rw [sq, abs_mul_abs_self]
  rw [jb_split x m]
  refine ⟨?_, ?_, ?_⟩
  · calc |g x| * |B0579.pd 0 g x| *
          (B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ (-4 : ℝ))
        = ((|g x| * B0579.jb x ^ ((m + 4) / 2)) * (|B0579.pd 0 g x| * B0579.jb x ^ ((m + 4) / 2)))
            * B0579.jb x ^ (-4 : ℝ) := by ring
      _ ≤ (C * C) * B0579.jb x ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul a0 a1 (mul_nonneg (abs_nonneg _) hN) hC0) hQ
  · calc |g x| * |B0579.pd 1 g x| *
          (B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ (-4 : ℝ))
        = ((|g x| * B0579.jb x ^ ((m + 4) / 2)) * (|B0579.pd 1 g x| * B0579.jb x ^ ((m + 4) / 2)))
            * B0579.jb x ^ (-4 : ℝ) := by ring
      _ ≤ (C * C) * B0579.jb x ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul a0 a2 (mul_nonneg (abs_nonneg _) hN) hC0) hQ
  · calc g x ^ 2 *
          (B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ (-4 : ℝ))
        = ((|g x| * B0579.jb x ^ ((m + 4) / 2)) * (|g x| * B0579.jb x ^ ((m + 4) / 2)))
            * B0579.jb x ^ (-4 : ℝ) := by rw [e]; ring
      _ ≤ (C * C) * B0579.jb x ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul a0 a0 (mul_nonneg (abs_nonneg _) hN) hC0) hQ

/-- A point of the cylinder cell has `|q| ≤ c/2`. -/
theorem abs_fst_le_cyl {c : ℝ} {x : B0579.Plane} (hx : x ∈ UnforcedLeray.Cyl.cell c) :
    |x.1| ≤ c / 2 := by
  have h := hx.1
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2.le⟩

/-- Cell-restricted integrability from a pointwise majorant on the strip `|q| ≤ c/2`. -/
theorem integrableOn_cell_of_bound {c : ℝ} {f Q : B0579.Plane → ℝ}
    (hQ : IntegrableOn Q (UnforcedLeray.Cyl.cell c)) (hf : Continuous f)
    (hb : ∀ x : B0579.Plane, |x.1| ≤ c / 2 → ‖f x‖ ≤ Q x) :
    IntegrableOn f (UnforcedLeray.Cyl.cell c) :=
  Integrable.mono' hQ hf.aestronglyMeasurable
    ((ae_restrict_iff' (UnforcedLeray.Cyl.measurableSet_cell c)).2
      (ae_of_all _ fun x hx => hb x (abs_fst_le_cyl hx)))

theorem integrableOn_g2rho {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (m : ℝ) :
    IntegrableOn (fun z : B0579.Plane => g z ^ 2 * B0579.jb z ^ m) (UnforcedLeray.Cyl.cell c) := by
  obtain ⟨C, hC0, hC⟩ := g2rho_bound hg m
  refine integrableOn_cell_of_bound (Q := fun x => C * C * B0579.jb x ^ (-4 : ℝ))
    (integrable_jb_neg4.const_mul (C * C)).integrableOn
    ((hg.smooth.continuous.pow 2).mul (B0579.continuous_jb_rpow m)) (fun x hx => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (B0579.jb_pos x).le m))]
  exact (hC x hx).2.2

/-! ## Derivatives of the weight and the basic facts about `v` -/

theorem abs_pd0_rho_le (m : ℝ) (x : B0579.Plane) :
    |B0579.pd 0 (fun y => B0579.jb y ^ m) x| ≤ 2 * |m| * B0579.jb x ^ m := by
  have hJ := B0579.jb_pos x
  have hJm : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg hJ.le m
  have hq : |x.1| ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_abs x.1, sq_nonneg (|x.1| - 1), sq_nonneg x.2]
  have hr : |x.1| / B0579.jb x ≤ 1 := (div_le_one hJ).2 hq
  rw [B0579.pd_zero_jb_rpow, Real.rpow_sub_one hJ.ne']
  have key : |2 * x.1 * m * (B0579.jb x ^ m / B0579.jb x)|
      = 2 * |m| * (B0579.jb x ^ m * (|x.1| / B0579.jb x)) := by
    simp only [abs_mul, abs_div, abs_of_pos hJ, abs_of_nonneg hJm, abs_two]
    ring
  rw [key]
  have h1 : B0579.jb x ^ m * (|x.1| / B0579.jb x) ≤ B0579.jb x ^ m :=
    mul_le_of_le_one_right hJm hr
  exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) (abs_nonneg m))

theorem abs_pd1_rho_le (m : ℝ) (x : B0579.Plane) :
    |B0579.pd 1 (fun y => B0579.jb y ^ m) x| ≤ 2 * |m| * B0579.jb x ^ m := by
  have hJ := B0579.jb_pos x
  have hJm : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg hJ.le m
  have hq : |x.2| ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_abs x.2, sq_nonneg (|x.2| - 1), sq_nonneg x.1]
  have hr : |x.2| / B0579.jb x ≤ 1 := (div_le_one hJ).2 hq
  rw [B0579.pd_one_jb_rpow, Real.rpow_sub_one hJ.ne']
  have key : |2 * x.2 * m * (B0579.jb x ^ m / B0579.jb x)|
      = 2 * |m| * (B0579.jb x ^ m * (|x.2| / B0579.jb x)) := by
    simp only [abs_mul, abs_div, abs_of_pos hJ, abs_of_nonneg hJm, abs_two]
    ring
  rw [key]
  have h1 : B0579.jb x ^ m * (|x.2| / B0579.jb x) ≤ B0579.jb x ^ m :=
    mul_le_of_le_one_right hJm hr
  exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) (abs_nonneg m))

theorem contDiff_one_of_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : B0579.Plane → E} (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : ContDiff ℝ 1 φ :=
  h.of_le (by exact_mod_cast le_top)

theorem contDiff_slice {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {σ : ℝ} (hσ : 0 ≤ σ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => tr.v σ x) := by
  have hmap : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => (σ, x))
      (univ : Set B0579.Plane) :=
    ((contDiff_const (c := σ)).prodMk contDiff_id).contDiffOn
  have hmaps : MapsTo (fun x : B0579.Plane => (σ, x)) (univ : Set B0579.Plane)
      (Ici (0 : ℝ) ×ˢ (univ : Set B0579.Plane)) :=
    fun x _ => ⟨hσ, mem_univ x⟩
  have h := tr.isTrain.smooth_v.comp hmap hmaps
  exact contDiffOn_univ.1 h

theorem continuous_pd {φ : B0579.Plane → ℝ} (hφ : ContDiff ℝ 1 φ) (j : Fin 2) :
    Continuous fun x => B0579.pd j φ x := by
  unfold B0579.pd
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem pd0_eq_partialQ {φ : B0579.Plane → ℝ} (hφ : Differentiable ℝ φ) (z : B0579.Plane) :
    B0579.pd 0 φ z = UnforcedLeray.Cyl.partialQ φ z := by
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hφ]
  rfl

theorem pd1_eq_partialEta {φ : B0579.Plane → ℝ} (hφ : Differentiable ℝ φ) (z : B0579.Plane) :
    B0579.pd 1 φ z = UnforcedLeray.Cyl.partialEta φ z := by
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hφ]
  rfl

theorem partialQ_cut {g : B0579.Plane → ℝ} (hg : Differentiable ℝ g) (R : ℝ)
    (z : B0579.Plane) :
    UnforcedLeray.Cyl.partialQ (fun y => g y * cutF R y.2) z = B0579.pd 0 g z * cutF R z.2 := by
  rw [pd0_eq_partialQ hg]
  exact ((UnforcedLeray.Cyl.hasDerivAt_sliceQ hg z.1 z.2).mul_const (cutF R z.2)).deriv

theorem partialEta_cut {g : B0579.Plane → ℝ} (hg : Differentiable ℝ g) (R : ℝ)
    (z : B0579.Plane) :
    UnforcedLeray.Cyl.partialEta (fun y => g y * cutF R y.2) z =
      B0579.pd 1 g z * cutF R z.2 + g z * cutD R z.2 := by
  rw [pd1_eq_partialEta hg]
  exact ((UnforcedLeray.Cyl.hasDerivAt_sliceEta hg z.1 z.2).mul (hasDerivAt_cutF R z.2)).deriv

/-! ## The three integrands -/

/-- The transport integrand `g (v·∇g) ρ`, `ρ = jb^m`. -/
def Gf (v : B0579.Plane → UnforcedLeray.Cyl.Vec2) (g : B0579.Plane → ℝ) (m : ℝ)
    (z : B0579.Plane) : ℝ :=
  g z * (v z 0 * B0579.pd 0 g z + v z 1 * B0579.pd 1 g z) * B0579.jb z ^ m

/-- The right-hand integrand `g² (v·∇ρ)`, `ρ = jb^m`. -/
def Hf (v : B0579.Plane → UnforcedLeray.Cyl.Vec2) (g : B0579.Plane → ℝ) (m : ℝ)
    (z : B0579.Plane) : ℝ :=
  g z ^ 2 * (v z 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) z +
    v z 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) z)

/-- The cut-off remainder `χ χ' g² ρ v₁`. -/
def Lf (v : B0579.Plane → UnforcedLeray.Cyl.Vec2) (g : B0579.Plane → ℝ) (m R : ℝ)
    (z : B0579.Plane) : ℝ :=
  cutF R z.2 * cutD R z.2 * (g z ^ 2 * B0579.jb z ^ m * v z 1)

theorem continuous_Gf {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g : B0579.Plane → ℝ} {m : ℝ}
    (hv : ContDiff ℝ 1 v) (hg : ContDiff ℝ 1 g) : Continuous (Gf v g m) := by
  have hv0 : Continuous fun z => v z 0 :=
    ((EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  have hv1 : Continuous fun z => v z 1 :=
    ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  exact (hg.continuous.mul ((hv0.mul (continuous_pd hg 0)).add
    (hv1.mul (continuous_pd hg 1)))).mul (B0579.continuous_jb_rpow m)

theorem continuous_Hf {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g : B0579.Plane → ℝ} {m : ℝ}
    (hv : ContDiff ℝ 1 v) (hg : ContDiff ℝ 1 g) : Continuous (Hf v g m) := by
  have hρ : ContDiff ℝ 1 (fun y : B0579.Plane => B0579.jb y ^ m) :=
    contDiff_one_of_top (B0579.contDiff_jb_rpow m)
  have hv0 : Continuous fun z => v z 0 :=
    ((EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  have hv1 : Continuous fun z => v z 1 :=
    ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  exact (hg.continuous.pow 2).mul ((hv0.mul (continuous_pd hρ 0)).add
    (hv1.mul (continuous_pd hρ 1)))

theorem continuous_Lf {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g : B0579.Plane → ℝ} {m R : ℝ}
    (hv : ContDiff ℝ 1 v) (hg : ContDiff ℝ 1 g) : Continuous (Lf v g m R) := by
  have hv1 : Continuous fun z => v z 1 :=
    ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  have hF : Continuous fun z : B0579.Plane => cutF R z.2 :=
    (cutF_contDiff R).continuous.comp continuous_snd
  have hD : Continuous fun z : B0579.Plane => cutD R z.2 :=
    (continuous_cutD R).comp continuous_snd
  exact (hF.mul hD).mul (((hg.continuous.pow 2).mul (B0579.continuous_jb_rpow m)).mul hv1)

/-! ## Pointwise bounds -/

theorem norm_Gf_le {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g : B0579.Plane → ℝ} {m M C : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hC0 : 0 ≤ C) {x : B0579.Plane}
    (h0 : |g x| * |B0579.pd 0 g x| * B0579.jb x ^ m ≤ C * C * B0579.jb x ^ (-4 : ℝ))
    (h1 : |g x| * |B0579.pd 1 g x| * B0579.jb x ^ m ≤ C * C * B0579.jb x ^ (-4 : ℝ)) :
    ‖Gf v g m x‖ ≤ 2 * M * (C * C) * B0579.jb x ^ (-4 : ℝ) := by
  have hv0 : |v x 0| ≤ M := by linarith [abs_nonneg (v x 1), hM x]
  have hv1 : |v x 1| ≤ M := by linarith [abs_nonneg (v x 0), hM x]
  have hsum : |v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x|
      ≤ M * |B0579.pd 0 g x| + M * |B0579.pd 1 g x| := by
    calc |v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x|
        ≤ |v x 0 * B0579.pd 0 g x| + |v x 1 * B0579.pd 1 g x| := abs_add_le _ _
      _ = |v x 0| * |B0579.pd 0 g x| + |v x 1| * |B0579.pd 1 g x| := by rw [abs_mul, abs_mul]
      _ ≤ M * |B0579.pd 0 g x| + M * |B0579.pd 1 g x| :=
          add_le_add (mul_le_mul_of_nonneg_right hv0 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hv1 (abs_nonneg _))
  have hJ : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
  unfold Gf
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hJ]
  calc |g x| * |v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x| * B0579.jb x ^ m
      ≤ |g x| * (M * |B0579.pd 0 g x| + M * |B0579.pd 1 g x|) * B0579.jb x ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)) hJ
    _ = M * (|g x| * |B0579.pd 0 g x| * B0579.jb x ^ m)
          + M * (|g x| * |B0579.pd 1 g x| * B0579.jb x ^ m) := by ring
    _ ≤ M * (C * C * B0579.jb x ^ (-4 : ℝ)) + M * (C * C * B0579.jb x ^ (-4 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 hM0) (mul_le_mul_of_nonneg_left h1 hM0)
    _ = 2 * M * (C * C) * B0579.jb x ^ (-4 : ℝ) := by ring

theorem norm_Hf_le {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g : B0579.Plane → ℝ} {m M C : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M) {x : B0579.Plane}
    (h2 : g x ^ 2 * B0579.jb x ^ m ≤ C * C * B0579.jb x ^ (-4 : ℝ)) :
    ‖Hf v g m x‖ ≤ 4 * M * |m| * (C * C) * B0579.jb x ^ (-4 : ℝ) := by
  have hv0 : |v x 0| ≤ M := by linarith [abs_nonneg (v x 1), hM x]
  have hv1 : |v x 1| ≤ M := by linarith [abs_nonneg (v x 0), hM x]
  have hP0 := abs_pd0_rho_le m x
  have hP1 := abs_pd1_rho_le m x
  have hsum : |v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
        v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x|
      ≤ M * |B0579.pd 0 (fun y => B0579.jb y ^ m) x| +
        M * |B0579.pd 1 (fun y => B0579.jb y ^ m) x| := by
    calc |v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
          v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x|
        ≤ |v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x| +
          |v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x| := abs_add_le _ _
      _ = |v x 0| * |B0579.pd 0 (fun y => B0579.jb y ^ m) x| +
          |v x 1| * |B0579.pd 1 (fun y => B0579.jb y ^ m) x| := by rw [abs_mul, abs_mul]
      _ ≤ M * |B0579.pd 0 (fun y => B0579.jb y ^ m) x| +
          M * |B0579.pd 1 (fun y => B0579.jb y ^ m) x| :=
          add_le_add (mul_le_mul_of_nonneg_right hv0 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hv1 (abs_nonneg _))
  unfold Hf
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc g x ^ 2 * |v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
          v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x|
      ≤ g x ^ 2 * (M * |B0579.pd 0 (fun y => B0579.jb y ^ m) x| +
          M * |B0579.pd 1 (fun y => B0579.jb y ^ m) x|) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ g x ^ 2 * (M * (2 * |m| * B0579.jb x ^ m) + M * (2 * |m| * B0579.jb x ^ m)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hP0 hM0) (mul_le_mul_of_nonneg_left hP1 hM0))
          (sq_nonneg _)
    _ = (4 * M * |m|) * (g x ^ 2 * B0579.jb x ^ m) := by ring
    _ ≤ (4 * M * |m|) * (C * C * B0579.jb x ^ (-4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg (by norm_num) hM0) (abs_nonneg m))
    _ = 4 * M * |m| * (C * C) * B0579.jb x ^ (-4 : ℝ) := by ring

theorem norm_Lf_le {v : B0579.Plane → UnforcedLeray.Cyl.Vec2} {g : B0579.Plane → ℝ}
    {m M K R : ℝ} (hK : 0 ≤ K) (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M)
    (hR : 0 < R) (hD : ∀ η, |cutD R η| ≤ K * (1 / R)) (z : B0579.Plane) :
    ‖Lf v g m R z‖ ≤ (K * M * (1 / R)) * (g z ^ 2 * B0579.jb z ^ m) := by
  have hJm : 0 ≤ B0579.jb z ^ m := Real.rpow_nonneg (B0579.jb_pos z).le m
  have hA : 0 ≤ g z ^ 2 * B0579.jb z ^ m := mul_nonneg (sq_nonneg _) hJm
  have hχ : |cutF R z.2| ≤ 1 := by
    rw [abs_of_nonneg (cutF_nonneg R z.2)]
    exact cutF_le_one R z.2
  have hv1 : |v z 1| ≤ M := by linarith [abs_nonneg (v z 0), hM z]
  unfold Lf
  rw [Real.norm_eq_abs]
  have e : |cutF R z.2 * cutD R z.2 * (g z ^ 2 * B0579.jb z ^ m * v z 1)|
      = |cutF R z.2| * |cutD R z.2| * ((g z ^ 2 * B0579.jb z ^ m) * |v z 1|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hA]
  rw [e]
  have hK' : 0 ≤ K * (1 / R) := mul_nonneg hK (one_div_nonneg.2 hR.le)
  have h12 : |cutF R z.2| * |cutD R z.2| ≤ 1 * (K * (1 / R)) :=
    mul_le_mul hχ (hD z.2) (abs_nonneg _) zero_le_one
  have h123 : |cutF R z.2| * |cutD R z.2| * ((g z ^ 2 * B0579.jb z ^ m) * |v z 1|)
      ≤ 1 * (K * (1 / R)) * ((g z ^ 2 * B0579.jb z ^ m) * M) :=
    mul_le_mul h12 (mul_le_mul_of_nonneg_left hv1 hA) (mul_nonneg hA (abs_nonneg _))
      (mul_nonneg zero_le_one hK')
  calc _ ≤ 1 * (K * (1 / R)) * ((g z ^ 2 * B0579.jb z ^ m) * M) := h123
    _ = (K * M * (1 / R)) * (g z ^ 2 * B0579.jb z ^ m) := by ring

/-! ## Integrability -/

theorem integrable_Gf {c M : ℝ} {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    {g : B0579.Plane → ℝ} (hv : ContDiff ℝ 1 v) (hM0 : 0 ≤ M)
    (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hg : CylSmoothDecay c g) (m : ℝ) :
    IntegrableOn (Gf v g m) (UnforcedLeray.Cyl.cell c) := by
  obtain ⟨C, hC0, hC⟩ := g2rho_bound hg m
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  exact integrableOn_cell_of_bound (Q := fun x => 2 * M * (C * C) * B0579.jb x ^ (-4 : ℝ))
    (integrable_jb_neg4.const_mul (2 * M * (C * C))).integrableOn
    (continuous_Gf hv hg1) (fun x hx => norm_Gf_le hM0 hM hC0 (hC x hx).1 (hC x hx).2.1)

theorem integrable_Hf {c M : ℝ} {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    {g : B0579.Plane → ℝ} (hv : ContDiff ℝ 1 v) (hM0 : 0 ≤ M)
    (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hg : CylSmoothDecay c g) (m : ℝ) :
    IntegrableOn (Hf v g m) (UnforcedLeray.Cyl.cell c) := by
  obtain ⟨C, hC0, hC⟩ := g2rho_bound hg m
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  exact integrableOn_cell_of_bound (Q := fun x => 4 * M * |m| * (C * C) * B0579.jb x ^ (-4 : ℝ))
    (integrable_jb_neg4.const_mul (4 * M * |m| * (C * C))).integrableOn
    (continuous_Hf hv hg1) (fun x hx => norm_Hf_le hM0 hM (hC x hx).2.2)

theorem integrable_Lf {c M K R : ℝ} {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    {g : B0579.Plane → ℝ} (hv : ContDiff ℝ 1 v) (hK : 0 ≤ K) (hM0 : 0 ≤ M)
    (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hR : 0 < R) (hD : ∀ η, |cutD R η| ≤ K * (1 / R))
    (hg : CylSmoothDecay c g) (m : ℝ) :
    IntegrableOn (Lf v g m R) (UnforcedLeray.Cyl.cell c) := by
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  exact integrableOn_cell_of_bound (Q := fun z => K * M * (1 / R) * (g z ^ 2 * B0579.jb z ^ m))
    (Integrable.const_mul (integrableOn_g2rho hg m) (K * M * (1 / R)))
    (continuous_Lf hv hg1) (fun z _ => norm_Lf_le hK hM0 hM hR hD z)

theorem integrable_cut_mul {c R : ℝ} {f : B0579.Plane → ℝ} (hf : Continuous f)
    (hfi : IntegrableOn f (UnforcedLeray.Cyl.cell c)) :
    IntegrableOn (fun z : B0579.Plane => cutF R z.2 ^ 2 * f z) (UnforcedLeray.Cyl.cell c) := by
  refine hfi.norm.mono' ?_ (ae_of_all _ fun z => ?_)
  · exact ((((cutF_contDiff R).continuous.comp continuous_snd).pow 2).mul hf).aestronglyMeasurable
  · rw [norm_mul, norm_pow, Real.norm_of_nonneg (cutF_nonneg R z.2)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (cutF_nonneg R z.2) (cutF_le_one R z.2))

/-! ## Limits -/

theorem tendsto_cut_integral {c : ℝ} {f : B0579.Plane → ℝ} (hf : Continuous f)
    (hfi : IntegrableOn f (UnforcedLeray.Cyl.cell c)) :
    Tendsto (fun n : ℕ => ∫ z in UnforcedLeray.Cyl.cell c, cutF ((n : ℝ) + 1) z.2 ^ 2 * f z)
      atTop (𝓝 (∫ z in UnforcedLeray.Cyl.cell c, f z)) := by
  have hcont : ∀ n : ℕ, Continuous fun z : B0579.Plane => cutF ((n : ℝ) + 1) z.2 ^ 2 * f z :=
    fun n => (((cutF_contDiff _).continuous.comp continuous_snd).pow 2).mul hf
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖f z‖)
    (Eventually.of_forall fun n => (hcont n).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ fun z => ?_) hfi.norm
    (ae_of_all _ fun z => ?_)
  · rw [norm_mul, norm_pow, Real.norm_of_nonneg (cutF_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (cutF_nonneg _ _) (cutF_le_one _ _))
  · have hev : (fun n : ℕ => cutF ((n : ℝ) + 1) z.2 ^ 2 * f z) =ᶠ[atTop]
        fun _ : ℕ => f z := by
      filter_upwards [eventually_ge_atTop ⌈|z.2|⌉₊] with n hn
      have h1 : |z.2| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have hc1 : cutF ((n : ℝ) + 1) z.2 = 1 := cutF_eq_one (by positivity) (by linarith)
      rw [hc1, one_pow, one_mul]
    exact tendsto_const_nhds.congr' hev.symm

theorem tendsto_Lf {c K M : ℝ} {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    {g : B0579.Plane → ℝ} {m : ℝ} (hK : 0 ≤ K) (hM0 : 0 ≤ M)
    (hM : ∀ x, |v x 0| + |v x 1| ≤ M)
    (hD : ∀ R η : ℝ, 0 < R → |cutD R η| ≤ K * (1 / R)) (hg : CylSmoothDecay c g) :
    Tendsto (fun n : ℕ => ∫ z in UnforcedLeray.Cyl.cell c, Lf v g m ((n : ℝ) + 1) z)
      atTop (𝓝 0) := by
  have h' : Tendsto (fun n : ℕ => K * M * (1 / ((n : ℝ) + 1)) *
      ∫ z in UnforcedLeray.Cyl.cell c, g z ^ 2 * B0579.jb z ^ m) atTop (𝓝 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (K * M)).mul_const
      (∫ z in UnforcedLeray.Cyl.cell c, g z ^ 2 * B0579.jb z ^ m))
    simpa using this
  refine squeeze_zero_norm (fun n : ℕ => ?_) h'
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hint := norm_integral_le_of_norm_le
    (Integrable.const_mul (integrableOn_g2rho hg m) (K * M * (1 / ((n : ℝ) + 1))))
    (ae_of_all _ fun z => norm_Lf_le hK hM0 hM hR (fun η => hD _ η hR) z)
  rw [integral_const_mul] at hint
  exact hint

/-! ## The transport identity for one cut-off -/

theorem transport_identity {c : ℝ} (hc : 0 < c) {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    (hv : ContDiff ℝ 1 v) (hvp : UnforcedLeray.Cyl.IsPeriodic c v)
    (hdiv : ∀ z, UnforcedLeray.Cyl.divergence v z = 0)
    {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (m : ℝ) {K M R : ℝ} (hK : 0 ≤ K)
    (hM0 : 0 ≤ M) (hM : ∀ x, |v x 0| + |v x 1| ≤ M) (hR : 0 < R)
    (hD : ∀ η, |cutD R η| ≤ K * (1 / R))
    (hI1 : IntegrableOn (Gf v g m) (UnforcedLeray.Cyl.cell c)) :
    (∫ z in UnforcedLeray.Cyl.cell c, cutF R z.2 ^ 2 * Gf v g m z) +
        ∫ z in UnforcedLeray.Cyl.cell c, Lf v g m R z
      = -(1 / 2) * ∫ z in UnforcedLeray.Cyl.cell c, cutF R z.2 ^ 2 * Hf v g m z := by
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have hgd : Differentiable ℝ g := hg1.differentiable (by norm_num)
  have hρ1 : ContDiff ℝ 1 (fun y : B0579.Plane => B0579.jb y ^ m) :=
    contDiff_one_of_top (B0579.contDiff_jb_rpow m)
  have hρd : Differentiable ℝ (fun y : B0579.Plane => B0579.jb y ^ m) :=
    hρ1.differentiable (by norm_num)
  have hcut1 : ContDiff ℝ 1 (fun z : B0579.Plane => cutF R z.2) :=
    contDiff_one_of_top ((cutF_contDiff R).comp contDiff_snd)
  have hw1 : ContDiff ℝ 1 (fun z : B0579.Plane => g z * cutF R z.2) := hg1.mul hcut1
  have hwp : UnforcedLeray.Cyl.IsPeriodic c (fun z : B0579.Plane => g z * cutF R z.2) := by
    intro z
    show g (z.1 + c, z.2) * cutF R z.2 = g z * cutF R z.2
    rw [hg.periodic z]
  have hwv : UnforcedLeray.Cyl.VanishesOutside (2 * R)
      (fun z : B0579.Plane => g z * cutF R z.2) := by
    intro z hz
    show g z * cutF R z.2 = 0
    rw [cutF_eq_zero hR hz.le, mul_zero]
  have hρseam : ∀ η : ℝ, (fun y : B0579.Plane => B0579.jb y ^ m) (-c / 2, η) =
      (fun y : B0579.Plane => B0579.jb y ^ m) (c / 2, η) := by
    intro η
    show B0579.jb (-c / 2, η) ^ m = B0579.jb (c / 2, η) ^ m
    congr 1
    simp only [B0579.jb, neg_div, neg_sq]
  have T : ∫ z in UnforcedLeray.Cyl.cell c,
        (v z 0 * UnforcedLeray.Cyl.partialQ (fun y : B0579.Plane => g y * cutF R y.2) z +
          v z 1 * UnforcedLeray.Cyl.partialEta (fun y : B0579.Plane => g y * cutF R y.2) z) *
          (g z * cutF R z.2) * B0579.jb z ^ m
      = -(1 / 2) * ∫ z in UnforcedLeray.Cyl.cell c, (g z * cutF R z.2) ^ 2 *
          (v z 0 * UnforcedLeray.Cyl.partialQ (fun y : B0579.Plane => B0579.jb y ^ m) z +
            v z 1 * UnforcedLeray.Cyl.partialEta (fun y : B0579.Plane => B0579.jb y ^ m) z) :=
    UnforcedLeray.Cyl.transport_antisymm (R := 2 * R) hc hv hw1 hρ1 hvp hwp hρseam hdiv hwv
  have eL : ∀ z : B0579.Plane,
      (v z 0 * UnforcedLeray.Cyl.partialQ (fun y : B0579.Plane => g y * cutF R y.2) z +
          v z 1 * UnforcedLeray.Cyl.partialEta (fun y : B0579.Plane => g y * cutF R y.2) z) *
          (g z * cutF R z.2) * B0579.jb z ^ m
        = cutF R z.2 ^ 2 * Gf v g m z + Lf v g m R z := by
    intro z
    rw [partialQ_cut hgd, partialEta_cut hgd]
    unfold Gf Lf
    ring
  have eR : ∀ z : B0579.Plane,
      (g z * cutF R z.2) ^ 2 *
          (v z 0 * UnforcedLeray.Cyl.partialQ (fun y : B0579.Plane => B0579.jb y ^ m) z +
            v z 1 * UnforcedLeray.Cyl.partialEta (fun y : B0579.Plane => B0579.jb y ^ m) z)
        = cutF R z.2 ^ 2 * Hf v g m z := by
    intro z
    rw [← pd0_eq_partialQ hρd z, ← pd1_eq_partialEta hρd z]
    unfold Hf
    ring
  simp only [eL, eR] at T
  have int1 : IntegrableOn (fun z : B0579.Plane => cutF R z.2 ^ 2 * Gf v g m z)
      (UnforcedLeray.Cyl.cell c) :=
    integrable_cut_mul (continuous_Gf hv hg1) hI1
  have int2 : IntegrableOn (fun z : B0579.Plane => Lf v g m R z)
      (UnforcedLeray.Cyl.cell c) :=
    integrable_Lf hv hK hM0 hM hR hD hg m
  rw [integral_add int1 int2] at T
  exact T

/-! ## The core statement for a fixed velocity -/

theorem core {c M : ℝ} (hc : 0 < c) {v : B0579.Plane → UnforcedLeray.Cyl.Vec2}
    (hv : ContDiff ℝ 1 v) (hvp : UnforcedLeray.Cyl.IsPeriodic c v)
    (hdiv : ∀ z, UnforcedLeray.Cyl.divergence v z = 0) (hM0 : 0 ≤ M)
    (hM : ∀ x, |v x 0| + |v x 1| ≤ M) {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (m : ℝ) :
    IntegrableOn (Gf v g m) (UnforcedLeray.Cyl.cell c) ∧
      IntegrableOn (Hf v g m) (UnforcedLeray.Cyl.cell c) ∧
      ∫ z in UnforcedLeray.Cyl.cell c, Gf v g m z =
        -(1 / 2) * ∫ z in UnforcedLeray.Cyl.cell c, Hf v g m z := by
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have hI1 : IntegrableOn (Gf v g m) (UnforcedLeray.Cyl.cell c) :=
    integrable_Gf hv hM0 hM hg m
  have hI2 : IntegrableOn (Hf v g m) (UnforcedLeray.Cyl.cell c) :=
    integrable_Hf hv hM0 hM hg m
  refine ⟨hI1, hI2, ?_⟩
  obtain ⟨K, hK0, hK⟩ := exists_cutD_bound
  have tA := tendsto_cut_integral (continuous_Gf hv hg1) hI1
  have tH := tendsto_cut_integral (continuous_Hf hv hg1) hI2
  have tL := tendsto_Lf (c := c) (v := v) (g := g) (m := m) hK0 hM0 hM hK hg
  have hid : ∀ n : ℕ,
      (∫ z in UnforcedLeray.Cyl.cell c, cutF ((n : ℝ) + 1) z.2 ^ 2 * Gf v g m z) +
          ∫ z in UnforcedLeray.Cyl.cell c, Lf v g m ((n : ℝ) + 1) z
        = -(1 / 2) * ∫ z in UnforcedLeray.Cyl.cell c, cutF ((n : ℝ) + 1) z.2 ^ 2 * Hf v g m z :=
    fun n => transport_identity hc hv hvp hdiv hg m hK0 hM0 hM (by positivity)
      (fun η => hK ((n : ℝ) + 1) η (by positivity)) hI1
  have h1 := tA.add tL
  have h2 := tH.const_mul (-(1 / 2))
  have h3 := tendsto_nhds_unique (h1.congr hid) h2
  rw [add_zero] at h3
  exact h3

end TransportIBP

/-! ## The target -/

/-- **Leaf 5 of `PartII-b:T22`: the transport term** (SP 2092-2093, 2097-2101). -/
theorem cylTransportIBP : CylTransportIBP := by
  intro ν c tr σ hσ hc hM m g hg
  obtain ⟨M, hM⟩ := hM
  have hv : ContDiff ℝ 1 (tr.v σ) :=
    TransportIBP.contDiff_one_of_top (TransportIBP.contDiff_slice tr hσ)
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hM 0)
  obtain ⟨h1, h2, h3⟩ := TransportIBP.core hc hv (tr.isTrain.periodic_v σ hσ)
    (tr.isTrain.solenoidal σ hσ) hM0 hM hg m
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  simp only [B0579.coe_density]
  rw [hcell]
  simp only [TransportIBP.Gf, TransportIBP.Hf] at h3
  refine ⟨h1, h2, ?_⟩
  linarith

end UnforcedLeray.Short.IIb
