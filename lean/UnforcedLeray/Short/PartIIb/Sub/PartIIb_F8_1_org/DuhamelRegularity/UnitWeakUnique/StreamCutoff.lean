import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.UnitWeakUnique.HeatMollifier
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.PeriodizeTest

/-!
# `UnitWeakUnique.StreamCutoff`: Telescoping `q`-partition of unity and stream-function lift of
cylinder tests to planar solenoidal tests

Helper module for `PartII-b:F8/1/org/3/2` (`CylUnitWeakHomogeneousUnique`).
Imports only frozen specification/library modules and `UnitWeakUnique.HeatMollifier`.
All declarations live inside `UnforcedLeray.Short.IIb.UnitWeakUniqueAux` (R6).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.UnitWeakUniqueAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.HeatCylinder

/-! ## 1. Telescoping smooth `q`-partition of unity `∑_{k ∈ ℤ} χ(q + k c) = 1` -/

/-- Smooth monotone step from `0` (`q ≤ -c/2`) to `1` (`q ≥ c/2`). -/
def qStep (c q : ℝ) : ℝ :=
  Real.smoothTransition ((q + c / 2) / c)

/-- Compactly supported smooth `q`-cutoff whose `c`-translates sum identically to `1`. -/
def qPartCutoff (c q : ℝ) : ℝ :=
  qStep c (q + c) - qStep c q

lemma contDiff_qPartCutoff (c : ℝ) : ContDiff ℝ ∞ (qPartCutoff c) := by
  have hs : ContDiff ℝ ∞ (qStep c) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const c)
  exact (hs.comp (contDiff_id.add contDiff_const)).sub hs

lemma qStep_eq_zero_of_le {c q : ℝ} (hc : 0 < c) (hq : q ≤ -(c / 2)) : qStep c q = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le)

lemma qStep_eq_one_of_ge {c q : ℝ} (hc : 0 < c) (hq : c / 2 ≤ q) : qStep c q = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ hc).2 (by linarith))

lemma qPartCutoff_eq_zero_of_abs {c q : ℝ} (hc : 0 < c) (hq : 2 * c ≤ |q|) :
    qPartCutoff c q = 0 := by
  rcases le_or_gt 0 q with hnn | hneg
  · rw [abs_of_nonneg hnn] at hq
    simp [qPartCutoff, qStep_eq_one_of_ge hc (by linarith : c / 2 ≤ q + c),
      qStep_eq_one_of_ge hc (by linarith : c / 2 ≤ q)]
  · rw [abs_of_neg hneg] at hq
    simp [qPartCutoff, qStep_eq_zero_of_le hc (by linarith : q + c ≤ -(c / 2)),
      qStep_eq_zero_of_le hc (by linarith : q ≤ -(c / 2))]

lemma tsum_qPartCutoff {c : ℝ} (hc : 0 < c) (q : ℝ) :
    (∑' k : ℤ, qPartCutoff c (q + (k : ℝ) * c)) = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((|q| + 2 * c) / c + 1)
  let idx : ℕ → ℤ := fun j => -(N : ℤ) + (j : ℤ)
  have hidx_inj : Function.Injective idx := fun j₁ j₂ h => by
    dsimp [idx] at h; omega
  let S : Finset ℤ := (Finset.range (2 * N + 1)).image idx
  have hout : ∀ k : ℤ, k ∉ S → qPartCutoff c (q + (k : ℝ) * c) = 0 := by
    intro k hk
    have hk_out : k < -(N : ℤ) ∨ (N : ℤ) < k := by
      by_contra h_in
      push Not at h_in
      apply hk
      rw [Finset.mem_image]
      refine ⟨(k + (N : ℤ)).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · dsimp [idx]; omega
    have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
      have hk_int : (N : ℤ) + 1 ≤ |k| := by
        rcases hk_out with hlt | hgt
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_nonneg (by omega)]; omega
      have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
      simpa [Int.cast_abs] using hk_r
    have h1 : |q| + 2 * c + c < ((N : ℝ) + 1) * c := by
      have hm := mul_lt_mul_of_pos_right hN hc
      have hdiv : ((|q| + 2 * c) / c + 1) * c = |q| + 2 * c + c := by field_simp [hc.ne']
      linarith
    have h2 : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
    have h3 : |(k : ℝ)| * c - |q| ≤ |q + (k : ℝ) * c| := by
      have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) q
      rw [add_comm, abs_mul, abs_of_pos hc] at hsub
      linarith
    exact qPartCutoff_eq_zero_of_abs hc (by linarith)
  rw [tsum_eq_sum hout, Finset.sum_image (fun j₁ _ j₂ _ h => hidx_inj h)]
  let g : ℕ → ℝ := fun j => qStep c (q + ((idx j : ℤ) : ℝ) * c)
  have hterm : ∀ j : ℕ, qPartCutoff c (q + ((idx j : ℤ) : ℝ) * c) = g (j + 1) - g j := by
    intro j
    dsimp [qPartCutoff, g, idx]
    congr 2
    push_cast
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub g (2 * N + 1)]
  have h1 : |q| + 2 * c + c < ((N : ℝ) + 1) * c := by
    have hm := mul_lt_mul_of_pos_right hN hc
    have hdiv : ((|q| + 2 * c) / c + 1) * c = |q| + 2 * c + c := by field_simp [hc.ne']
    linarith
  have hq_lo : -|q| ≤ q := neg_abs_le q
  have hq_hi : q ≤ |q| := le_abs_self q
  have htop : g (2 * N + 1) = 1 := by
    dsimp [g, idx]
    apply qStep_eq_one_of_ge hc
    push_cast
    linarith
  have hbot : g 0 = 0 := by
    dsimp [g, idx]
    apply qStep_eq_zero_of_le hc
    push_cast
    linarith
  rw [htop, hbot, sub_zero]

/-! ## 2. Compact interval enclosure for `tsupport α ⊆ Ioo 0 1` -/

lemma exists_Icc_subset_Ioo_of_tsupport {α : ℝ → ℝ}
    (hα_cp : HasCompactSupport α) (hα_ts : tsupport α ⊆ Ioo 0 1) :
    ∃ a₀ b₀ : ℝ, 0 < a₀ ∧ a₀ ≤ b₀ ∧ b₀ < 1 ∧ tsupport α ⊆ Icc a₀ b₀ := by
  by_cases hne : (tsupport α).Nonempty
  · obtain ⟨a₀, ha₀_mem, ha₀_min⟩ := hα_cp.exists_isMinOn hne continuousOn_id
    obtain ⟨b₀, hb₀_mem, hb₀_max⟩ := hα_cp.exists_isMaxOn hne continuousOn_id
    exact ⟨a₀, b₀, (hα_ts ha₀_mem).1, ha₀_min hb₀_mem, (hα_ts hb₀_mem).2,
      fun r hr => ⟨ha₀_min hr, hb₀_max hr⟩⟩
  · rw [not_nonempty_iff_eq_empty] at hne
    exact ⟨1 / 4, 3 / 4, by norm_num, by norm_num, by norm_num,
      by rw [hne]; exact empty_subset _⟩

/-! ## 3. Stream-function lift `(α, φ) ↦ Ψ` and exact `qPeriodize` formulas -/

/-- Spatial localized stream factor `ψ₀(z) = qPartCutoff c z.1 * φ z`. -/
def streamPlane (c : ℝ) (φ : B0579.Plane → ℝ) (z : B0579.Plane) : ℝ :=
  qPartCutoff c z.1 * φ z

/-- Space-time stream function `θ(s, z) = α(s - σ) * qPartCutoff c z.1 * φ z`. -/
def streamCoord (c σ : ℝ) (α : ℝ → ℝ) (φ : B0579.Plane → ℝ) (x : Coord) : ℝ :=
  α (x.1 - σ) * streamPlane c φ x.2

/-- Planar solenoidal test `Ψ = (∂_η θ, -∂_q θ)` built from `(α, φ)`. -/
def streamPlanarTest (c σ : ℝ) (α : ℝ → ℝ) (φ : B0579.Plane → ℝ) (x : Coord) : Fin 2 → ℝ :=
  ![cpd 2 (streamCoord c σ α φ) x, -cpd 1 (streamCoord c σ α φ) x]

/-- Real coordinate of `meridTranspose ν Ψ`. -/
def meridTransposeR (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℝ :=
  -cpd 0 (fun y => Ψ y i) x -
    ν * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)

lemma meridTranspose_eq_cast (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) :
    meridTranspose ν Ψ x i = (meridTransposeR ν Ψ x i : ℂ) := by
  simp [meridTranspose, meridTransposeR]

private lemma periodic_int_mul {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (z : B0579.Plane) (k : ℤ) :
    φ (z.1 + (k : ℝ) * c, z.2) = φ z := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    push_cast at ih ⊢
    have hstep : (z.1 + ((n : ℝ) + 1) * c, z.2) = (z.1 + (n : ℝ) * c + c, z.2) := by
      ext <;> simp; ring
    rw [hstep, hφ.periodic (z.1 + (n : ℝ) * c, z.2), ih]
  | pred n ih =>
    push_cast at ih ⊢
    have hstep : (z.1 + (-(n : ℝ) - 1) * c + c, z.2) = (z.1 + (-(n : ℝ)) * c, z.2) := by
      ext <;> simp; ring
    have hp := hφ.periodic (z.1 + (-(n : ℝ) - 1) * c, z.2)
    rw [hstep] at hp
    exact hp.symm.trans ih

lemma qPeriodize_streamCoord {c σ : ℝ} (hc : 0 < c) (α : ℝ → ℝ)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (s : ℝ) (z : B0579.Plane) :
    TailPeriodizeAux.qPeriodize c (streamCoord c σ α φ) s z = α (s - σ) * φ z := by
  unfold TailPeriodizeAux.qPeriodize streamCoord streamPlane
  have heq : (fun k : ℤ => α (s - σ) * (qPartCutoff c (z.1 + (k : ℝ) * c) *
      φ (z.1 + (k : ℝ) * c, z.2))) =
      fun k : ℤ => (α (s - σ) * φ z) * qPartCutoff c (z.1 + (k : ℝ) * c) := by
    funext k
    rw [periodic_int_mul hφ z k]
    ring
  simp_rw [heq]
  rw [tsum_mul_left, tsum_qPartCutoff hc z.1, mul_one]

private lemma pd_const_mul {j : Fin 2} (a : ℝ) {g : B0579.Plane → ℝ} {z : B0579.Plane}
    (hg : DifferentiableAt ℝ g z) :
    B0579.pd j (fun w => a * g w) z = a * B0579.pd j g z := by
  unfold B0579.pd
  rw [fderiv_const_mul hg, smul_apply, smul_eq_mul]

private lemma cpd_sep_zero {σ : ℝ} {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α)
    {ψ : B0579.Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : Coord) :
    cpd 0 (fun y : Coord => α (y.1 - σ) * ψ y.2) x = deriv α (x.1 - σ) * ψ x.2 := by
  have h_in : HasFDerivAt (fun y : Coord => y.1 - σ)
      (ContinuousLinearMap.fst ℝ ℝ B0579.Plane) x := by
    simpa using (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := B0579.Plane) (p := x)).sub_const σ
  have hdα : HasFDerivAt (fun y : Coord => α (y.1 - σ))
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv α (x.1 - σ))).comp
        (ContinuousLinearMap.fst ℝ ℝ B0579.Plane)) x :=
    (((hα.differentiable (by simp) (x.1 - σ)).hasDerivAt).hasFDerivAt).comp x h_in
  have hdψ : HasFDerivAt (fun y : Coord => ψ y.2)
      ((fderiv ℝ ψ x.2).comp (ContinuousLinearMap.snd ℝ ℝ B0579.Plane)) x :=
    ((hψ.differentiable (by simp) x.2).hasFDerivAt).comp x hasFDerivAt_snd
  have hmul : fderiv ℝ (fun y : Coord => α (y.1 - σ) * ψ y.2) x = _ := (hdα.mul hdψ).fderiv
  unfold cpd
  rw [hmul]
  have hz0 : ((0 : ℝ), (0 : ℝ)) = (0 : B0579.Plane) := rfl
  simp [cdir, hz0]
  ring

private lemma cpd_sep_succ {σ : ℝ} {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α)
    {ψ : B0579.Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : Fin 2) (x : Coord) :
    cpd j.succ (fun y : Coord => α (y.1 - σ) * ψ y.2) x =
      α (x.1 - σ) * B0579.pd j ψ x.2 := by
  have h_in : HasFDerivAt (fun y : Coord => y.1 - σ)
      (ContinuousLinearMap.fst ℝ ℝ B0579.Plane) x := by
    simpa using (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := B0579.Plane) (p := x)).sub_const σ
  have hdα : HasFDerivAt (fun y : Coord => α (y.1 - σ))
      ((fderiv ℝ α (x.1 - σ)).comp (ContinuousLinearMap.fst ℝ ℝ B0579.Plane)) x :=
    ((hα.differentiable (by simp) (x.1 - σ)).hasFDerivAt).comp x h_in
  have hdψ : HasFDerivAt (fun y : Coord => ψ y.2)
      ((fderiv ℝ ψ x.2).comp (ContinuousLinearMap.snd ℝ ℝ B0579.Plane)) x :=
    ((hψ.differentiable (by simp) x.2).hasFDerivAt).comp x hasFDerivAt_snd
  have hmul : fderiv ℝ (fun y : Coord => α (y.1 - σ) * ψ y.2) x = _ := (hdα.mul hdψ).fderiv
  unfold cpd B0579.pd
  rw [hmul]
  fin_cases j <;> simp [cdir, B0579.dir]

lemma isCoordTest_sep {c σ a₀ b₀ R : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ)
    (ha₀ : 0 < a₀) (hb₀ : b₀ < 1) (hR : 0 < R)
    {β : ℝ → ℝ} (hβ_sm : ContDiff ℝ ∞ β) (hβ_van : ∀ r, r ∉ Icc a₀ b₀ → β r = 0)
    {ψ : B0579.Plane → ℝ} (hψ_sm : ContDiff ℝ ∞ ψ)
    (hψ_van : ∀ z : B0579.Plane, (2 * c < |z.1| ∨ R < |z.2|) → ψ z = 0) :
    IsCoordTest (fun x : Coord => β (x.1 - σ) * ψ x.2) ∧
      tsupport (fun x : Coord => β (x.1 - σ) * ψ x.2) ⊆
        Icc (σ + a₀) (σ + b₀) ×ˢ (Icc (-(2 * c)) (2 * c) ×ˢ Icc (-R) R) := by
  let f : Coord → ℝ := fun x => β (x.1 - σ) * ψ x.2
  let K : Set Coord := Icc (σ + a₀) (σ + b₀) ×ˢ (Icc (-(2 * c)) (2 * c) ×ˢ Icc (-R) R)
  have hK_closed : IsClosed K := isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)
  have hK_comp : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hts : tsupport f ⊆ K := by
    refine closure_minimal (fun x hx => ?_) hK_closed
    by_contra hnot
    apply hx
    dsimp [f]
    by_cases hs : x.1 ∈ Icc (σ + a₀) (σ + b₀)
    · have hz : 2 * c < |x.2.1| ∨ R < |x.2.2| := by
        by_contra hz'
        push Not at hz'
        exact hnot ⟨hs, abs_le.1 hz'.1, abs_le.1 hz'.2⟩
      rw [hψ_van x.2 hz, mul_zero]
    · have hr : x.1 - σ ∉ Icc a₀ b₀ := fun hr => hs ⟨by linarith [hr.1], by linarith [hr.2]⟩
      rw [hβ_van (x.1 - σ) hr, zero_mul]
  have hf_sm : ContDiff ℝ ∞ f :=
    (hβ_sm.comp (contDiff_fst.sub contDiff_const)).mul (hψ_sm.comp contDiff_snd)
  have hf_cp : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hK_comp
    (subset_tsupport f |>.trans hts)
  refine ⟨⟨hf_sm, hf_cp, fun x hx => ?_⟩, hts⟩
  have _ := hc; have _ := hb₀; have _ := hR
  have hx1 : σ + a₀ ≤ x.1 := (hts hx).1.1
  rw [mem_prod, mem_Ioi]
  exact ⟨by linarith, mem_univ _⟩

lemma streamCoord_isCoordTest {c σ a₀ b₀ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ)
    (ha₀ : 0 < a₀) (hb₀ : b₀ < 1)
    {β : ℝ → ℝ} (hβ_sm : ContDiff ℝ ∞ β) (hβ_van : ∀ r, r ∉ Icc a₀ b₀ → β r = 0)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∃ R : ℝ, 0 < R ∧ IsCoordTest (streamCoord c σ β φ) ∧
      tsupport (streamCoord c σ β φ) ⊆
        Icc (σ + a₀) (σ + b₀) ×ˢ (Icc (-(2 * c)) (2 * c) ×ˢ Icc (-R) R) := by
  obtain ⟨R₀, hR₀⟩ := hφ.band
  let R : ℝ := max (max R₀ 1) (2 * c)
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hψ_sm : ContDiff ℝ ∞ (streamPlane c φ) :=
    ((contDiff_qPartCutoff c).comp contDiff_fst).mul hφ.smooth
  have hψ_van : ∀ z : B0579.Plane, (2 * c < |z.1| ∨ R < |z.2|) → streamPlane c φ z = 0 := by
    intro z hz
    dsimp [streamPlane]
    rcases hz with hq | hη
    · rw [qPartCutoff_eq_zero_of_abs hc hq.le, zero_mul]
    · have hR₀_lt : R₀ < |z.2| :=
        lt_of_le_of_lt ((le_max_left R₀ 1).trans (le_max_left _ _)) hη
      rw [hR₀ z hR₀_lt, mul_zero]
  obtain ⟨hc_test, hts⟩ := isCoordTest_sep hc hσ ha₀ hb₀ hR_pos hβ_sm hβ_van hψ_sm hψ_van
  exact ⟨R, hR_pos, hc_test, hts⟩

lemma streamPlanarTest_props {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ)
    {α : ℝ → ℝ} (hα_sm : ContDiff ℝ ∞ α) (hα_cp : HasCompactSupport α)
    (hα_ts : tsupport α ⊆ Ioo 0 1)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    let Ψ := streamPlanarTest c σ α φ
    IsPlanarSolTest Ψ ∧
      (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo σ (σ + 1) ×ˢ univ) ∧
      (∃ a₀ b₀ R : ℝ, 0 < a₀ ∧ a₀ ≤ b₀ ∧ b₀ < 1 ∧ 0 < R ∧
        (∀ r, r ∉ Icc a₀ b₀ → α r = 0 ∧ deriv α r = 0) ∧
        (∀ x : Coord, (x.1 ∉ Icc (σ + a₀) (σ + b₀) ∨ R < |x.2.1| ∨ R < |x.2.2|) →
          ∀ i : Fin 2, Ψ x i = 0 ∧ ∀ ν : ℝ, meridTransposeR ν Ψ x i = 0)) ∧
      (∀ (s : ℝ) (z : B0579.Plane) (i : Fin 2),
        TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s z =
          α (s - σ) * UnforcedLeray.Cyl.rotT φ z i) ∧
      (∀ (ν s : ℝ) (z : B0579.Plane) (i : Fin 2),
        TailPeriodizeAux.qPeriodize c (fun x => meridTransposeR ν Ψ x i) s z =
          -deriv α (s - σ) * UnforcedLeray.Cyl.rotT φ z i -
            ν * α (s - σ) *
              (B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z +
                B0579.pd 1 (B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z)) := by
  intro Ψ
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub_ab⟩ := exists_Icc_subset_Ioo_of_tsupport hα_cp hα_ts
  have hα_van : ∀ r, r ∉ Icc a₀ b₀ → α r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport (fun hm => hr (hsub_ab hm))
  have hdα_van : ∀ r, r ∉ Icc a₀ b₀ → deriv α r = 0 := by
    intro r hr
    have hnot : r ∉ tsupport α := fun hm => hr (hsub_ab hm)
    exact ((notMem_tsupport_iff_eventuallyEq.1 hnot).deriv).eq_of_nhds.trans (by simp)
  obtain ⟨R₁, hR₁_pos, hθ_test, hθ_ts⟩ :=
    streamCoord_isCoordTest hc hσ ha₀ hb₀ hα_sm hα_van hφ
  have hdα_sm : ContDiff ℝ ∞ (deriv α) := hα_sm.deriv'
  obtain ⟨R₂, hR₂_pos, hθ'_test, _⟩ :=
    streamCoord_isCoordTest hc hσ ha₀ hb₀ hdα_sm hdα_van hφ
  have _ := hR₂_pos
  let R : ℝ := max R₁ (2 * c)
  have hR_pos : 0 < R := lt_of_lt_of_le hR₁_pos (le_max_left _ _)
  let Box : Set Coord := Icc (σ + a₀) (σ + b₀) ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hθ_ts_box : tsupport (streamCoord c σ α φ) ⊆ Box := by
    refine hθ_ts.trans (prod_mono Subset.rfl (prod_mono ?_ ?_))
    · exact Icc_subset_Icc (neg_le_neg (le_max_right _ _)) (le_max_right _ _)
    · exact Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _)
  have hψ_sm : ContDiff ℝ ∞ (streamPlane c φ) :=
    ((contDiff_qPartCutoff c).comp contDiff_fst).mul hφ.smooth
  have hΨ0_eq : (fun x => Ψ x 0) = cpd 2 (streamCoord c σ α φ) := rfl
  have hcpd_test : ∀ {f : Coord → ℝ}, IsCoordTest f → ∀ j : Fin 3,
      IsCoordTest (cpd j f) ∧ tsupport (cpd j f) ⊆ tsupport f := by
    intro f hf j
    have hsm : ContDiff ℝ ∞ (cpd j f) := by
      unfold cpd
      exact (hf.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hsub : tsupport (cpd j f) ⊆ tsupport f := by
      refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
      by_contra hnot
      have hev := notMem_tsupport_iff_eventuallyEq.1 hnot
      exact hx (by unfold cpd; simp [hev.fderiv_eq])
    exact ⟨⟨hsm, HasCompactSupport.of_support_subset_isCompact hf.compact
      ((subset_tsupport _).trans hsub), hsub.trans hf.supp⟩, hsub⟩
  have hΨ0_test : IsCoordTest (fun x => Ψ x 0) := by
    rw [hΨ0_eq]; exact (hcpd_test hθ_test 2).1
  have hΨ1_test : IsCoordTest (fun x => Ψ x 1) := by
    have h1 := (hcpd_test hθ_test 1).1
    refine ⟨h1.smooth.neg, h1.compact.neg, ?_⟩
    change tsupport (-(cpd 1 (streamCoord c σ α φ))) ⊆ _
    rw [tsupport_neg]
    exact h1.supp
  have hΨ_ts_box : ∀ i : Fin 2, tsupport (fun x => Ψ x i) ⊆ Box := by
    intro i
    fin_cases i
    · exact (hcpd_test hθ_test 2).2.trans hθ_ts_box
    · change tsupport (-(cpd 1 (streamCoord c σ α φ))) ⊆ Box
      rw [tsupport_neg]
      exact (hcpd_test hθ_test 1).2.trans hθ_ts_box
  have hΨ_sol : IsPlanarSolTest Ψ := by
    refine ⟨fun i => by fin_cases i; exact hΨ0_test; exact hΨ1_test, fun x => ?_⟩
    have h0 : (fun y => Ψ y 0) = fun y => α (y.1 - σ) * B0579.pd 1 (streamPlane c φ) y.2 := by
      funext y; exact cpd_sep_succ hα_sm hψ_sm 1 y
    have h1 : (fun y => Ψ y 1) = fun y => -(α (y.1 - σ) * B0579.pd 0 (streamPlane c φ) y.2) := by
      funext y; exact congrArg Neg.neg (cpd_sep_succ hα_sm hψ_sm 0 y)
    have hp0_sm : ContDiff ℝ ∞ (B0579.pd 0 (streamPlane c φ)) :=
      (hψ_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hp1_sm : ContDiff ℝ ∞ (B0579.pd 1 (streamPlane c φ)) :=
      (hψ_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hd1 : cpd 1 (fun y => Ψ y 0) x =
        α (x.1 - σ) * B0579.pd 0 (B0579.pd 1 (streamPlane c φ)) x.2 := by
      rw [h0]; exact cpd_sep_succ hα_sm hp1_sm 0 x
    have hd2 : cpd 2 (fun y => Ψ y 1) x =
        -(α (x.1 - σ) * B0579.pd 1 (B0579.pd 0 (streamPlane c φ)) x.2) := by
      rw [h1]
      unfold cpd
      rw [fderiv_fun_neg, neg_apply]
      exact congrArg Neg.neg (cpd_sep_succ hα_sm hp0_sm 1 x)
    have hcomm : B0579.pd 0 (B0579.pd 1 (streamPlane c φ)) x.2 =
        B0579.pd 1 (B0579.pd 0 (streamPlane c φ)) x.2 := by
      have hp := UnforcedLeray.Sob.iterDirDeriv_perm
        (List.Perm.swap ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) []) hψ_sm
      exact congrFun hp x.2
    rw [hd1, hd2, hcomm]
    ring
  have hΨ_supp_Ioo : ∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo σ (σ + 1) ×ˢ univ := by
    intro i x hx
    have hxB := hΨ_ts_box i hx
    rw [mem_prod, mem_Ioo]
    exact ⟨⟨by linarith [hxB.1.1], by linarith [hxB.1.2]⟩, mem_univ _⟩
  have hrot_eq : ∀ z : B0579.Plane,
      UnforcedLeray.Cyl.rotT φ z 0 = B0579.pd 1 φ z ∧
      UnforcedLeray.Cyl.rotT φ z 1 = -B0579.pd 0 φ z := by
    intro z
    have hdφ := hφ.differentiable
    exact ⟨UnforcedLeray.Cyl.partialEta_eq_fderiv hdφ z,
      congrArg Neg.neg (UnforcedLeray.Cyl.partialQ_eq_fderiv hdφ z)⟩
  have hqPer_Ψ : ∀ (β : ℝ → ℝ) (hθβ : IsCoordTest (streamCoord c σ β φ))
      (s : ℝ) (z : B0579.Plane) (i : Fin 2),
      TailPeriodizeAux.qPeriodize c (fun x => streamPlanarTest c σ β φ x i) s z =
        β (s - σ) * UnforcedLeray.Cyl.rotT φ z i := by
    intro β hθβ s z i
    have hqθ : TailPeriodizeAux.qPeriodize c (streamCoord c σ β φ) s =
        fun w => β (s - σ) * φ w := funext (qPeriodize_streamCoord hc β hφ s)
    fin_cases i
    · have hp : B0579.pd 1 (TailPeriodizeAux.qPeriodize c (streamCoord c σ β φ) s) z =
          TailPeriodizeAux.qPeriodize c (cpd 2 (streamCoord c σ β φ)) s z :=
        TailPeriodizeAux.pd_qPeriodize hc hθβ s 1 z
      change TailPeriodizeAux.qPeriodize c (cpd 2 (streamCoord c σ β φ)) s z =
        β (s - σ) * UnforcedLeray.Cyl.rotT φ z 0
      rw [← hp, hqθ, (hrot_eq z).1]
      exact pd_const_mul (β (s - σ)) (hφ.differentiable z)
    · have hp : B0579.pd 0 (TailPeriodizeAux.qPeriodize c (streamCoord c σ β φ) s) z =
          TailPeriodizeAux.qPeriodize c (cpd 1 (streamCoord c σ β φ)) s z :=
        TailPeriodizeAux.pd_qPeriodize hc hθβ s 0 z
      have hneg : TailPeriodizeAux.qPeriodize c (fun x => -cpd 1 (streamCoord c σ β φ) x) s z =
          -TailPeriodizeAux.qPeriodize c (cpd 1 (streamCoord c σ β φ)) s z := by
        unfold TailPeriodizeAux.qPeriodize; exact tsum_neg
      change TailPeriodizeAux.qPeriodize c (fun x => -cpd 1 (streamCoord c σ β φ) x) s z =
        β (s - σ) * UnforcedLeray.Cyl.rotT φ z 1
      rw [hneg, ← hp, hqθ, (hrot_eq z).2, pd_const_mul (β (s - σ)) (hφ.differentiable z)]
      ring
  have hcpd0_Ψ : ∀ (x : Coord) (i : Fin 2),
      cpd 0 (fun y => Ψ y i) x = streamPlanarTest c σ (deriv α) φ x i := by
    intro x i
    have hp0_sm : ContDiff ℝ ∞ (B0579.pd 0 (streamPlane c φ)) :=
      (hψ_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hp1_sm : ContDiff ℝ ∞ (B0579.pd 1 (streamPlane c φ)) :=
      (hψ_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    fin_cases i
    · change cpd 0 (fun y => Ψ y 0) x = streamPlanarTest c σ (deriv α) φ x 0
      have h0 : (fun y => Ψ y 0) = fun y => α (y.1 - σ) * B0579.pd 1 (streamPlane c φ) y.2 :=
        funext (cpd_sep_succ hα_sm hψ_sm 1)
      rw [h0, cpd_sep_zero hα_sm hp1_sm x]
      exact (cpd_sep_succ hdα_sm hψ_sm 1 x).symm
    · change cpd 0 (fun y => Ψ y 1) x = streamPlanarTest c σ (deriv α) φ x 1
      have h1 : (fun y => Ψ y 1) =
          fun y => -(α (y.1 - σ) * B0579.pd 0 (streamPlane c φ) y.2) :=
        funext fun y => congrArg Neg.neg (cpd_sep_succ hα_sm hψ_sm 0 y)
      rw [h1]
      unfold cpd
      rw [fderiv_fun_neg, neg_apply]
      exact congrArg Neg.neg ((cpd_sep_zero hα_sm hp0_sm x).trans
        (cpd_sep_succ hdα_sm hψ_sm 0 x).symm)
  refine ⟨hΨ_sol, hΨ_supp_Ioo, ⟨a₀, b₀, R, ha₀, hab₀, hb₀, hR_pos,
    fun r hr => ⟨hα_van r hr, hdα_van r hr⟩, ?_⟩,
    hqPer_Ψ α hθ_test, ?_⟩
  · intro x hx i
    have hnotB : x ∉ Box := by
      intro hm
      rcases hx with hs | hq | hη
      · exact hs hm.1
      · exact not_le.2 hq (abs_le.2 hm.2.1)
      · exact not_le.2 hη (abs_le.2 hm.2.2)
    have hnot_ts : x ∉ tsupport (fun y => Ψ y i) := fun hm => hnotB (hΨ_ts_box i hm)
    have hΨi_t : IsCoordTest (fun y => Ψ y i) := hΨ_sol.smooth i
    have hΨ0 : Ψ x i = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) hnot_ts
    have hc0 : cpd 0 (fun y => Ψ y i) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm => hnot_ts ((hcpd_test hΨi_t 0).2 hm))
    have hc11 : cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm =>
        hnot_ts ((hcpd_test hΨi_t 1).2 ((hcpd_test (hcpd_test hΨi_t 1).1 1).2 hm)))
    have hc22 : cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm =>
        hnot_ts ((hcpd_test hΨi_t 2).2 ((hcpd_test (hcpd_test hΨi_t 2).1 2).2 hm)))
    exact ⟨hΨ0, fun ν => by simp [meridTransposeR, hc0, hc11, hc22]⟩
  · intro ν s z i
    have hΨi_test : IsCoordTest (fun x => Ψ x i) := hΨ_sol.smooth i
    have hΨi_1 : IsCoordTest (cpd 1 (fun x => Ψ x i)) := (hcpd_test hΨi_test 1).1
    have hΨi_2 : IsCoordTest (cpd 2 (fun x => Ψ x i)) := (hcpd_test hΨi_test 2).1
    obtain ⟨_, _, R_i, _, _, _, hbox_i⟩ := TailPeriodizeAux.coordTest_box hΨi_test
    obtain ⟨_, _, R_t, _, _, _, hbox_t⟩ :=
      TailPeriodizeAux.coordTest_box ((hcpd_test hΨi_test 0).1)
    obtain ⟨_, _, R_11, _, _, _, hbox_11⟩ :=
      TailPeriodizeAux.coordTest_box ((hcpd_test hΨi_1 1).1)
    obtain ⟨_, _, R_22, _, _, _, hbox_22⟩ :=
      TailPeriodizeAux.coordTest_box ((hcpd_test hΨi_2 2).1)
    have _ := hbox_i
    let Rm := max (max R_i R_t) (max R_11 R_22)
    obtain ⟨N, hN⟩ := exists_nat_gt ((|z.1| + Rm) / c + 1)
    let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
    have hout_q : ∀ k ∉ S, Rm < |z.1 + (k : ℝ) * c| := by
      intro k hk
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
      have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
        have hk_int : (N : ℤ) + 1 ≤ |k| := by
          rcases hk with hk | hk
          · rw [abs_of_neg (by omega)]; omega
          · rw [abs_of_nonneg (by omega)]; omega
        have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
        simpa [Int.cast_abs] using hk_r
      have h1 : |z.1| + Rm + c < ((N : ℝ) + 1) * c := by
        have hm := mul_lt_mul_of_pos_right hN hc
        have hdiv : ((|z.1| + Rm) / c + 1) * c = |z.1| + Rm + c := by field_simp [hc.ne']
        linarith
      have h2 : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
      have h3 : |(k : ℝ)| * c - |z.1| ≤ |z.1 + (k : ℝ) * c| := by
        have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) z.1
        rw [add_comm, abs_mul, abs_of_pos hc] at hsub
        linarith
      linarith
    have hsum_t : TailPeriodizeAux.qPeriodize c (cpd 0 (fun y => Ψ y i)) s z =
        ∑ k ∈ S, cpd 0 (fun y => Ψ y i) (s, (z.1 + (k : ℝ) * c, z.2)) :=
      tsum_eq_sum fun k hk => (hbox_t _ (Or.inr (Or.inl
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) (hout_q k hk))))).1
    have hsum_11 : TailPeriodizeAux.qPeriodize c
        (cpd 1 (fun y => cpd 1 (fun w => Ψ w i) y)) s z =
        ∑ k ∈ S, cpd 1 (fun y => cpd 1 (fun w => Ψ w i) y) (s, (z.1 + (k : ℝ) * c, z.2)) :=
      tsum_eq_sum fun k hk => (hbox_11 _ (Or.inr (Or.inl
        (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (hout_q k hk))))).1
    have hsum_22 : TailPeriodizeAux.qPeriodize c
        (cpd 2 (fun y => cpd 2 (fun w => Ψ w i) y)) s z =
        ∑ k ∈ S, cpd 2 (fun y => cpd 2 (fun w => Ψ w i) y) (s, (z.1 + (k : ℝ) * c, z.2)) :=
      tsum_eq_sum fun k hk => (hbox_22 _ (Or.inr (Or.inl
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) (hout_q k hk))))).1
    have hsum_m : TailPeriodizeAux.qPeriodize c (fun x => meridTransposeR ν Ψ x i) s z =
        ∑ k ∈ S, meridTransposeR ν Ψ (s, (z.1 + (k : ℝ) * c, z.2)) i := by
      refine tsum_eq_sum fun k hk => ?_
      have v0 := (hbox_t (s, (z.1 + (k : ℝ) * c, z.2)) (Or.inr (Or.inl
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) (hout_q k hk))))).1
      have v1 := (hbox_11 (s, (z.1 + (k : ℝ) * c, z.2)) (Or.inr (Or.inl
        (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (hout_q k hk))))).1
      have v2 := (hbox_22 (s, (z.1 + (k : ℝ) * c, z.2)) (Or.inr (Or.inl
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) (hout_q k hk))))).1
      simp [meridTransposeR, v0, v1, v2]
    have hlin : TailPeriodizeAux.qPeriodize c (fun x => meridTransposeR ν Ψ x i) s z =
        -TailPeriodizeAux.qPeriodize c (cpd 0 (fun y => Ψ y i)) s z -
          ν * (TailPeriodizeAux.qPeriodize c
              (cpd 1 (fun y => cpd 1 (fun w => Ψ w i) y)) s z +
            TailPeriodizeAux.qPeriodize c
              (cpd 2 (fun y => cpd 2 (fun w => Ψ w i) y)) s z) := by
      rw [hsum_m, hsum_t, hsum_11, hsum_22]
      simp only [meridTransposeR, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum]
    have h0_val : TailPeriodizeAux.qPeriodize c (cpd 0 (fun y => Ψ y i)) s z =
        deriv α (s - σ) * UnforcedLeray.Cyl.rotT φ z i := by
      have heq_fn : cpd 0 (fun y => Ψ y i) = fun x => streamPlanarTest c σ (deriv α) φ x i :=
        funext fun x => hcpd0_Ψ x i
      rw [heq_fn]
      exact hqPer_Ψ (deriv α) hθ'_test s z i
    have hq_Ψi : TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s =
        fun w => α (s - σ) * UnforcedLeray.Cyl.rotT φ w i :=
      funext fun w => hqPer_Ψ α hθ_test s w i
    have hrot_i_diff : ContDiff ℝ ∞ (fun w => UnforcedLeray.Cyl.rotT φ w i) :=
      ((isRealSolCylTest_rotT ((isCylTest_sob_iff c φ).2 hφ)).cyl_test i).smooth
    have h11_val : TailPeriodizeAux.qPeriodize c
        (cpd 1 (fun y => cpd 1 (fun w => Ψ w i) y)) s z =
        α (s - σ) * B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z := by
      have hp11 : B0579.pd 0 (TailPeriodizeAux.qPeriodize c (cpd 1 (fun w => Ψ w i)) s) z =
          TailPeriodizeAux.qPeriodize c (cpd 1 (fun y => cpd 1 (fun w => Ψ w i) y)) s z :=
        TailPeriodizeAux.pd_qPeriodize hc hΨi_1 s 0 z
      rw [← hp11]
      have h1_fn : TailPeriodizeAux.qPeriodize c (cpd 1 (fun w => Ψ w i)) s =
          B0579.pd 0 (TailPeriodizeAux.qPeriodize c (fun w => Ψ w i) s) :=
        funext fun w => (TailPeriodizeAux.pd_qPeriodize hc hΨi_test s 0 w).symm
      rw [h1_fn, hq_Ψi]
      have hp1 : B0579.pd 0 (fun w => α (s - σ) * UnforcedLeray.Cyl.rotT φ w i) =
          fun w => α (s - σ) * B0579.pd 0 (fun u => UnforcedLeray.Cyl.rotT φ u i) w :=
        funext fun w => pd_const_mul (α (s - σ)) (hrot_i_diff.differentiable (by simp) w)
      have hp1_diff : Differentiable ℝ (B0579.pd 0 (fun u => UnforcedLeray.Cyl.rotT φ u i)) :=
        (((isRealSolCylTest_rotT ((isCylTest_sob_iff c φ).2 hφ)).cyl_test i).pd 0).differentiable
      rw [hp1]
      exact pd_const_mul (α (s - σ)) (hp1_diff z)
    have h22_val : TailPeriodizeAux.qPeriodize c
        (cpd 2 (fun y => cpd 2 (fun w => Ψ w i) y)) s z =
        α (s - σ) * B0579.pd 1 (B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z := by
      have hp22 : B0579.pd 1 (TailPeriodizeAux.qPeriodize c (cpd 2 (fun w => Ψ w i)) s) z =
          TailPeriodizeAux.qPeriodize c (cpd 2 (fun y => cpd 2 (fun w => Ψ w i) y)) s z :=
        TailPeriodizeAux.pd_qPeriodize hc hΨi_2 s 1 z
      rw [← hp22]
      have h2_fn : TailPeriodizeAux.qPeriodize c (cpd 2 (fun w => Ψ w i)) s =
          B0579.pd 1 (TailPeriodizeAux.qPeriodize c (fun w => Ψ w i) s) :=
        funext fun w => (TailPeriodizeAux.pd_qPeriodize hc hΨi_test s 1 w).symm
      rw [h2_fn, hq_Ψi]
      have hp2 : B0579.pd 1 (fun w => α (s - σ) * UnforcedLeray.Cyl.rotT φ w i) =
          fun w => α (s - σ) * B0579.pd 1 (fun u => UnforcedLeray.Cyl.rotT φ u i) w :=
        funext fun w => pd_const_mul (α (s - σ)) (hrot_i_diff.differentiable (by simp) w)
      have hp2_diff : Differentiable ℝ (B0579.pd 1 (fun u => UnforcedLeray.Cyl.rotT φ u i)) :=
        (((isRealSolCylTest_rotT ((isCylTest_sob_iff c φ).2 hφ)).cyl_test i).pd 1).differentiable
      rw [hp2]
      exact pd_const_mul (α (s - σ)) (hp2_diff z)
    rw [hlin, h0_val, h11_val, h22_val]
    ring

end UnforcedLeray.Short.IIb.UnitWeakUniqueAux
