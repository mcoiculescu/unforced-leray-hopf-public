import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T23
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy

/-!
# Part II-b, task `PartII-b:T23/1`: `FreeCylSmoothExists`

Source of record: `the November 2 reference manuscript`, lines 2100-2114.
For a smooth cylinder test datum `B0579.IsCylTest c f` and a BUC train `tr`, the regular flows on
each finite horizon `[s, s + N + 1]` glue to a global flow `w` on `[s, ∞)` that restricts to
`IsRegularCylFlow c ν tr.v s T w` on every `[s, T]` and satisfies `IsFreeCylFlow m tr s f w`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- Time-dependent pairing identity and interval integrability for a regular cylinder flow
without `TrainClose` (assembled from `rtdSlice`, `rtdLapIBP`, `rtdTransportIBP`, `rtdCont`,
`rtdHasDeriv`, `rtdRhsBound`, `rtdFTC`). -/
private theorem rtd_of_regular {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {s T : ℝ} {u : ℝ → B0579.Plane → ℝ} (hs : 0 ≤ s)
    (hω : IsRegularCylFlow c ν tr.v s T u)
    {t₁ : ℝ} {φ : ℝ → B0579.Plane → ℝ} (hst : s ≤ t₁) (ht₁ : t₁ ≤ T)
    (hφ : CylEtaTest c s t₁ φ)
    (hM : ∃ M : ℝ, ∀ r ∈ Icc s T, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) :
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, u r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))) volume s t₁ ∧
    (∫ x in B0579.cell c, u t₁ x * φ t₁ x) - ∫ x in B0579.cell c, u s x * φ s x =
      ∫ r in s..t₁, ∫ x in B0579.cell c, u r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)) := by
  have hD : ∀ r ∈ Ioo s t₁, HasDerivAt (fun r' => ∫ x in B0579.cell c, u r' x * φ r' x)
      (∫ x in B0579.cell c, u r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))) r := by
    intro r hr
    obtain ⟨hi, hd⟩ := rtdHasDeriv ν c tr s T t₁ u φ hc hs hst ht₁ hω hφ hφ.decay_r hM r hr
    have hrT : r ∈ Icc s T := ⟨hr.1.le, hr.2.le.trans ht₁⟩
    have hg := hω.slice r hrT
    have hh := rtdSlice c s t₁ φ hφ r ⟨hr.1.le, hr.2.le⟩
    obtain ⟨M, hM'⟩ := hM
    obtain ⟨iL1, iL2, eL⟩ := rtdLapIBP c hc (u r) (φ r) hg hh
    obtain ⟨iT1, iT2, eT⟩ :=
      rtdTransportIBP ν c tr r (hs.trans hr.1.le) hc ⟨M, hM' r hrT⟩ (u r) (φ r) hg hh
    convert hd using 1
    have eA : (fun x => u r x * (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
        (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))) =
        fun x => (u r x * deriv (fun r' => φ r' x) r + ν * (u r x * lapP (φ r) x)) +
          u r x * (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x) := by
      funext x; ring
    have eB : (fun x => (ν * lapP (u r) x -
        (tr.v r x 0 * B0579.pd 0 (u r) x + tr.v r x 1 * B0579.pd 1 (u r) x)) * φ r x +
          u r x * deriv (fun r' => φ r' x) r) =
        fun x => (ν * (lapP (u r) x * φ r x) -
          (tr.v r x 0 * B0579.pd 0 (u r) x + tr.v r x 1 * B0579.pd 1 (u r) x) * φ r x) +
          u r x * deriv (fun r' => φ r' x) r := by
      funext x; ring
    have jL1 : IntegrableOn (fun x => ν * (lapP (u r) x * φ r x)) (B0579.cell c) :=
      iL1.const_mul ν
    have jL2 : IntegrableOn (fun x => ν * (u r x * lapP (φ r) x)) (B0579.cell c) :=
      iL2.const_mul ν
    have j1 : IntegrableOn (fun x => u r x * deriv (fun r' => φ r' x) r +
        ν * (u r x * lapP (φ r) x)) (B0579.cell c) := hi.add jL2
    have j2 : IntegrableOn (fun x => ν * (lapP (u r) x * φ r x) -
        (tr.v r x 0 * B0579.pd 0 (u r) x + tr.v r x 1 * B0579.pd 1 (u r) x) * φ r x)
        (B0579.cell c) := jL1.sub iT1
    rw [eA, eB, integral_add j1 iT2, integral_add hi jL2, integral_add j2 hi,
      integral_sub jL1 iT1, integral_const_mul, integral_const_mul, eL, eT]
    ring
  have hbd := rtdRhsBound ν c tr s T t₁ u φ hc hst ht₁ hω hφ hφ.decay_r hM
  have hcont := rtdCont ν c tr s T t₁ u φ hc hst ht₁ hω hφ
  have hFTC := rtdFTC (fun r' => ∫ x in B0579.cell c, u r' x * φ r' x)
    (fun r => ∫ x in B0579.cell c, u r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))) s t₁ hst
    hcont hD hbd
  refine ⟨?_, hFTC.symm⟩
  obtain ⟨C, hC⟩ := hbd
  have hmeas : AEStronglyMeasurable
      (fun r => ∫ x in B0579.cell c, u r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)))
      (volume.restrict (Ioo s t₁)) := by
    refine (measurable_deriv (fun r' => ∫ x in B0579.cell c, u r' x * φ r' x)).aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hD r hr).deriv
  have hconst : IntegrableOn (fun _ : ℝ => C) (Ioo s t₁) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hint : IntegrableOn
      (fun r => ∫ x in B0579.cell c, u r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)))
      (Ioo s t₁) := by
    refine Integrable.mono' hconst hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs]
    exact hC r hr
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
  exact hint.congr_set_ae Ioo_ae_eq_Ioc.symm

/-- Two continuous `c`-periodic functions on the plane that agree a.e. on `B0579.cell c` are equal
everywhere on the plane. -/
private theorem eq_of_ae_eq_cell_of_periodic {c : ℝ} (hc : 0 < c) {f g : B0579.Plane → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hpf : ∀ x : B0579.Plane, f (x.1 + c, x.2) = f x)
    (hpg : ∀ x : B0579.Plane, g (x.1 + c, x.2) = g x)
    (hae : f =ᵐ[volume.restrict (B0579.cell c)] g) : f = g := by
  have hsub : Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) ⊆ B0579.cell c :=
    prod_mono Ioo_subset_Ico_self Subset.rfl
  have hopen : IsOpen (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have haeU : f =ᵐ[volume.restrict (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))] g :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have heqU : EqOn f g (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) :=
    Measure.eqOn_open_of_ae_eq haeU hopen hf.continuousOn hg.continuousOn
  have hclos : B0579.cell c ⊆ closure (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioo (by linarith), closure_univ]
    exact prod_mono Ico_subset_Icc_self Subset.rfl
  have heqCell : EqOn f g (B0579.cell c) :=
    heqU.of_subset_closure hf.continuousOn hg.continuousOn hsub hclos
  funext x
  set n : ℤ := ⌊(x.1 + c / 2) / c⌋ with hn
  have hmem : ((x.1 - n * c, x.2) : B0579.Plane) ∈ B0579.cell c := by
    refine Set.mk_mem_prod ?_ (Set.mem_univ _)
    have := qwrap_mem_Ico hc x.1
    unfold qwrap at this
    rw [← hn] at this
    rwa [mul_comm] at this
  have hper_f : Function.Periodic (fun q : ℝ => f (q, x.2)) c := fun q => hpf (q, x.2)
  have hper_g : Function.Periodic (fun q : ℝ => g (q, x.2)) c := fun q => hpg (q, x.2)
  have hf_shift : f (x.1 - n * c, x.2) = f x := hper_f.sub_int_mul_eq n
  have hg_shift : g (x.1 - n * c, x.2) = g x := hper_g.sub_int_mul_eq n
  rw [← hf_shift, ← hg_shift]
  exact heqCell hmem

/-- Two regular cylinder flows starting from the same datum at age `s` agree pointwise at every
common age `t`. -/
private theorem regularCylFlow_unique_slice {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {s T₁ T₂ : ℝ} (hs : 0 ≤ s) {u₁ u₂ : ℝ → B0579.Plane → ℝ}
    (hu₁ : IsRegularCylFlow c ν tr.v s T₁ u₁)
    (hu₂ : IsRegularCylFlow c ν tr.v s T₂ u₂)
    (hinit : u₁ s = u₂ s)
    {t : ℝ} (ht₁ : t ∈ Icc s T₁) (ht₂ : t ∈ Icc s T₂) :
    u₁ t = u₂ t := by
  have hT : 0 ≤ max T₁ T₂ :=
    le_trans hs (le_trans ht₁.1 (le_trans ht₁.2 (le_max_left _ _)))
  obtain ⟨V, _, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu hT
  have hM₁ : ∀ r ∈ Icc s T₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ 2 * V := by
    intro r hr x
    have hr' : r ∈ Icc 0 (max T₁ T₂) := ⟨le_trans hs hr.1, le_trans hr.2 (le_max_left _ _)⟩
    linarith [(hV r hr' x 0).1, (hV r hr' x 1).1]
  have hM₂ : ∀ r ∈ Icc s T₂, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ 2 * V := by
    intro r hr x
    have hr' : r ∈ Icc 0 (max T₁ T₂) := ⟨le_trans hs hr.1, le_trans hr.2 (le_max_right _ _)⟩
    linarith [(hV r hr' x 0).1, (hV r hr' x 1).1]
  have hMt : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ 2 * V :=
    fun r hr x => hM₁ r ⟨hr.1, le_trans hr.2 ht₁.2⟩ x
  refine eq_of_ae_eq_cell_of_periodic hc
    (hu₁.slice t ht₁).smooth.continuous (hu₂.slice t ht₂).smooth.continuous
    (hu₁.slice t ht₁).periodic (hu₂.slice t ht₂).periodic ?_
  refine cylFundLemma c 0 hc le_rfl (u₁ t) (u₂ t)
    (cylRegularMem ν c 0 s T₁ tr.v u₁ hc le_rfl hu₁ t ht₁)
    (cylRegularMem ν c 0 s T₂ tr.v u₂ hc le_rfl hu₂ t ht₂) ?_
  intro ψ hψ
  obtain ⟨φ, hφt, hφ0, hPDE⟩ := bwdSolve_of_buc hν hc hbu hs ht₁.1 hψ
  have hφ : CylEtaTest c s t φ := hφ0.toCylEtaTest hν.le tr.v hMt hPDE
  have k1 := (rtd_of_regular hc tr hs hu₁ ht₁.1 ht₁.2 hφ ⟨2 * V, hM₁⟩).2
  have k2 := (rtd_of_regular hc tr hs hu₂ ht₂.1 ht₂.2 hφ ⟨2 * V, hM₂⟩).2
  rw [cyl_rhs_zero ht₁.1 u₁ φ tr.v _ hPDE, hφt, hinit] at k1
  rw [cyl_rhs_zero ht₁.1 u₂ φ tr.v _ hPDE, hφt] at k2
  linarith

/-- A time-independent cylinder test function `φ` defines a `CylEtaTest` on any `[s, t₁]`. -/
private theorem cylEtaTest_const {c s t₁ : ℝ} (hc : 0 < c) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) :
    CylEtaTest c s t₁ (fun _ x => φ x) where
  smooth := (hφ.smooth.comp contDiff_snd).contDiffOn
  periodic := fun _ _ x => hφ.periodic x
  decay := by
    intro N
    obtain ⟨B0, hB0⟩ := lztCylBounded hc hφ
    obtain ⟨B1, hB1⟩ := lztCylBounded hc (hφ.pd 0)
    obtain ⟨B2, hB2⟩ := lztCylBounded hc (hφ.pd 1)
    obtain ⟨B3, hB3⟩ := lztCylBounded hc ((hφ.pd 0).pd 0)
    obtain ⟨B4, hB4⟩ := lztCylBounded hc ((hφ.pd 1).pd 1)
    obtain ⟨R0, hR0⟩ := B0579.IsCylTest.exists_band_pd hφ 0
    obtain ⟨R1, hR1⟩ := B0579.IsCylTest.exists_band_pd hφ 1
    obtain ⟨R2, hR2⟩ := B0579.IsCylTest.exists_band_pd (hφ.pd 0) 0
    obtain ⟨R3, hR3⟩ := B0579.IsCylTest.exists_band_pd (hφ.pd 1) 1
    set R : ℝ := max (max R0 R1) (max R2 R3)
    set B : ℝ := |B0| + |B1| + |B2| + |B3| + |B4|
    set N' : ℝ := max N 0
    refine ⟨B * (1 + R ^ 2) ^ N', fun _ _ x => ?_⟩
    have hB_pos : 0 ≤ B := by positivity
    have hR_pos : 0 ≤ (1 + R ^ 2) ^ N' := Real.rpow_nonneg (by positivity) _
    by_cases hx : R < |x.2|
    · have hx0 : R0 < |x.2| := lt_of_le_of_lt (le_trans (le_max_left R0 R1) (le_max_left _ _)) hx
      have hx1 : R1 < |x.2| := lt_of_le_of_lt (le_trans (le_max_right R0 R1) (le_max_left _ _)) hx
      have hx2 : R2 < |x.2| := lt_of_le_of_lt (le_trans (le_max_left R2 R3) (le_max_right _ _)) hx
      have hx3 : R3 < |x.2| := lt_of_le_of_lt (le_trans (le_max_right R2 R3) (le_max_right _ _)) hx
      obtain ⟨hφx, hp0⟩ := hR0 x hx0
      obtain ⟨-, hp1⟩ := hR1 x hx1
      obtain ⟨-, hq00⟩ := hR2 x hx2
      obtain ⟨-, hq11⟩ := hR3 x hx3
      have hLP : lapP φ x = 0 := by
        unfold lapP
        simp [hq00, hq11]
      rw [hφx, hp0, hp1, hLP]
      simp only [abs_zero, add_zero, zero_mul]
      exact mul_nonneg hB_pos hR_pos
    · rw [not_lt] at hx
      have hsum : |φ x| + |B0579.pd 0 φ x| + |B0579.pd 1 φ x| + |lapP φ x| ≤ B := by
        have hL : |lapP φ x| ≤ |B3| + |B4| := by
          unfold lapP
          calc |B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x|
              ≤ |B0579.pd 0 (B0579.pd 0 φ) x| + |B0579.pd 1 (B0579.pd 1 φ) x| := abs_add_le _ _
            _ ≤ |B3| + |B4| :=
                add_le_add ((hB3 x).trans (le_abs_self B3)) ((hB4 x).trans (le_abs_self B4))
        have h0 := (hB0 x).trans (le_abs_self B0)
        have h1 := (hB1 x).trans (le_abs_self B1)
        have h2 := (hB2 x).trans (le_abs_self B2)
        dsimp [B]
        linarith
      have hR0' : 0 ≤ |x.2| := abs_nonneg x.2
      have hsq : x.2 ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs x.2]
        nlinarith [mul_nonneg (sub_nonneg.2 hx) (add_nonneg hR0' (le_trans hR0' hx))]
      have hw1 : (1 + x.2 ^ 2) ^ N ≤ (1 + x.2 ^ 2) ^ N' :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x.2]) (le_max_left _ _)
      have hw2 : (1 + x.2 ^ 2) ^ N' ≤ (1 + R ^ 2) ^ N' :=
        Real.rpow_le_rpow (by positivity) (by linarith) (le_max_right _ _)
      exact mul_le_mul hsum (le_trans hw1 hw2) (Real.rpow_nonneg (by positivity) _) hB_pos
  decay_r := by
    intro N
    refine ⟨0, fun r _ x => ?_⟩
    rw [deriv_const r (φ x), abs_zero, zero_mul]

/-- Right-continuity in `X_{m,c}` of a global regular cylinder flow `w` on `[s, ∞)`. -/
private theorem strongCont_of_regular {ν c m s : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    {v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec} {w : ℝ → B0579.Plane → ℝ}
    (hreg : ∀ T : ℝ, s ≤ T → IsRegularCylFlow c ν v s T w)
    (t : ℝ) (hst : s ≤ t) :
    Tendsto (fun t' => eLpNorm (w t' - w t) 2 (B0579.cellMeasure c m)) (𝓝[Ici s] t) (𝓝 0) := by
  have ht1 : s ≤ t + 1 := by linarith
  have hR := hreg (t + 1) ht1
  set N : ℝ := |m| + 2 with hNdef
  have hN1 : 1 < N + N - m := by
    rw [hNdef]
    linarith [le_abs_self m, abs_nonneg m]
  obtain ⟨C, hC⟩ := hR.cell_decay N
  have hbndI : IntegrableOn
      (fun x : B0579.Plane => (4 * C ^ 2) * B0579.jb x ^ (m - (N + N)))
      (B0579.cell c) :=
    ((regEnergyDeriv_integrable_jb m N hN1).const_mul _).integrableOn
  have hcont_x : ∀ σ ∈ Icc s (t + 1), Continuous (w σ) :=
    fun σ hσ => (hR.slice σ hσ).smooth.continuous
  have htI : t ∈ Icc s (t + 1) := ⟨hst, by linarith⟩
  have hdens_cont : Continuous fun x : B0579.Plane => (B0579.density m x : ℝ) := by
    simp only [B0579.coe_density]
    exact B0579.continuous_jb_rpow m
  have hjoint : ∀ x : B0579.Plane, ContinuousOn (fun σ => w σ x) (Icc s (t + 1)) := by
    intro x
    have h2 : ContinuousOn (fun σ : ℝ => (σ, x)) (Icc s (t + 1)) :=
      (continuous_id.prodMk continuous_const).continuousOn
    exact hR.jointCont.comp h2 (fun σ hσ => ⟨hσ, mem_univ x⟩)
  have hpt_bd : ∀ σ ∈ Icc s (t + 1), ∀ x ∈ B0579.cell c,
      ‖(w σ x - w t x) ^ 2 * (B0579.density m x : ℝ)‖ ≤
        (4 * C ^ 2) * B0579.jb x ^ (m - (N + N)) := by
    intro σ hσ x hx
    have hx' := abs_fst_le_of_mem_cell hx
    have hu : 0 < B0579.jb x ^ N := Real.rpow_pos_of_pos (B0579.jb_pos x) N
    have hw0 : 0 ≤ (B0579.density m x : ℝ) := (B0579.density_pos m x).le
    have hCσ : |w σ x| * B0579.jb x ^ N ≤ C := by
      have h := hC σ hσ x hx'
      have h0 : |w σ x| ≤ |w σ x| + |B0579.pd 0 (w σ) x| + |B0579.pd 1 (w σ) x| + |lapP (w σ) x| := by
        linarith [abs_nonneg (B0579.pd 0 (w σ) x), abs_nonneg (B0579.pd 1 (w σ) x),
          abs_nonneg (lapP (w σ) x)]
      exact le_trans (mul_le_mul_of_nonneg_right h0 hu.le) h
    have hCt : |w t x| * B0579.jb x ^ N ≤ C := by
      have h := hC t htI x hx'
      have h0 : |w t x| ≤ |w t x| + |B0579.pd 0 (w t) x| + |B0579.pd 1 (w t) x| + |lapP (w t) x| := by
        linarith [abs_nonneg (B0579.pd 0 (w t) x), abs_nonneg (B0579.pd 1 (w t) x),
          abs_nonneg (lapP (w t) x)]
      exact le_trans (mul_le_mul_of_nonneg_right h0 hu.le) h
    have hC0 : 0 ≤ C := le_trans (mul_nonneg (abs_nonneg _) hu.le) hCt
    have hdiff : |w σ x - w t x| * B0579.jb x ^ N ≤ 2 * C := by
      have h1 : |w σ x - w t x| ≤ |w σ x| + |w t x| := by
        simpa [sub_eq_add_neg] using abs_add_le (w σ x) (-w t x)
      have h2 := mul_le_mul_of_nonneg_right h1 hu.le
      linarith
    have hsq : (w σ x - w t x) ^ 2 * (B0579.jb x ^ N * B0579.jb x ^ N) ≤ 4 * C ^ 2 := by
      have h0 : 0 ≤ |w σ x - w t x| * B0579.jb x ^ N := mul_nonneg (abs_nonneg _) hu.le
      have h2 := mul_le_mul hdiff hdiff h0 (by linarith)
      calc (w σ x - w t x) ^ 2 * (B0579.jb x ^ N * B0579.jb x ^ N)
          = (|w σ x - w t x| * B0579.jb x ^ N) * (|w σ x - w t x| * B0579.jb x ^ N) := by
            rw [← sq_abs (w σ x - w t x)]; ring
        _ ≤ (2 * C) * (2 * C) := h2
        _ = 4 * C ^ 2 := by ring
    have hpos2 : 0 < B0579.jb x ^ N * B0579.jb x ^ N := mul_pos hu hu
    have hdiv : (w σ x - w t x) ^ 2 ≤ 4 * C ^ 2 / (B0579.jb x ^ N * B0579.jb x ^ N) :=
      (le_div_iff₀ hpos2).2 hsq
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw0), regEnergyDeriv_rpow_eq x m N]
    calc (w σ x - w t x) ^ 2 * (B0579.density m x : ℝ)
        ≤ (4 * C ^ 2 / (B0579.jb x ^ N * B0579.jb x ^ N)) * (B0579.density m x : ℝ) :=
          mul_le_mul_of_nonneg_right hdiv hw0
      _ = (4 * C ^ 2) * ((B0579.density m x : ℝ) / (B0579.jb x ^ N * B0579.jb x ^ N)) := by ring
  have hcontE : ContinuousOn
      (fun σ => cylEnergy c m (w σ - w t)) (Icc s (t + 1)) := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun x => (4 * C ^ 2) * B0579.jb x ^ (m - (N + N))) ?_ ?_ hbndI ?_
    · intro σ hσ
      exact ((((hcont_x σ hσ).sub (hcont_x t htI)).pow 2).mul hdens_cont).aestronglyMeasurable
    · intro σ hσ
      exact ae_restrict_of_forall_mem (B0579.measurableSet_cell c) (hpt_bd σ hσ)
    · refine MeasureTheory.ae_of_all _ (fun x => ?_)
      exact (((hjoint x).sub continuousOn_const).pow 2).mul continuousOn_const
  have hEt : cylEnergy c m (w t - w t) = 0 := by
    unfold cylEnergy
    simp [sub_self]
  have hnhds : Icc s (t + 1) ∈ 𝓝[Ici s] t := by
    refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : t < t + 1)))) ?_
    intro σ hσ
    exact ⟨hσ.1, le_of_lt hσ.2⟩
  have hlimE : Tendsto (fun σ => cylEnergy c m (w σ - w t)) (𝓝[Ici s] t) (𝓝 0) := by
    rw [← hEt]
    exact (hcontE t htI).mono_of_mem_nhdsWithin hnhds
  have hlimS : Tendsto (fun σ => ENNReal.ofReal (Real.sqrt (cylEnergy c m (w σ - w t))))
      (𝓝[Ici s] t) (𝓝 0) := by
    have h0 : ENNReal.ofReal (Real.sqrt 0) = 0 := by simp
    rw [← h0]
    exact ((ENNReal.continuous_ofReal.comp Real.continuous_sqrt).tendsto 0).comp hlimE
  refine hlimS.congr' ?_
  filter_upwards [hnhds] with σ hσ
  have hmσ : MemLp (w σ) 2 (B0579.cellMeasure c m) :=
    cylRegularMem ν c m s (t + 1) v w hc hm hR σ hσ
  have hmt : MemLp (w t) 2 (B0579.cellMeasure c m) :=
    cylRegularMem ν c m s (t + 1) v w hc hm hR t htI
  have hsub_mem : MemLp (w σ - w t) 2 (B0579.cellMeasure c m) := hmσ.sub hmt
  rw [← t22_energy_eq_sq_eLpNorm hsub_mem, Real.sqrt_sq ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (hsub_mem.eLpNorm_lt_top.ne)]

/-- **Main theorem (`PartII-b:T23/1`)**: global regular and weak cylinder flow for smooth test
data. -/
theorem freeCylSmoothExists_proof : UnforcedLeray.Short.IIb.FreeCylSmoothExists := by
  intro m ν c hm hν hc tr hbu s hs f hf
  have hTN : ∀ N : ℕ, s ≤ s + (N : ℝ) + 1 := fun N => by linarith [Nat.cast_nonneg (α := ℝ) N]
  choose u hu hus using fun (N : ℕ) => cylRegularExists_of_buc hν hc hbu hs (hTN N) hf
  let w : ℝ → B0579.Plane → ℝ := fun t => u ⌈t - s⌉₊ t
  have hw_eq : ∀ (N : ℕ) (t : ℝ), t ∈ Icc s (s + (N : ℝ) + 1) → w t = u N t := by
    intro N t ht
    have ht' : t ∈ Icc s (s + (⌈t - s⌉₊ : ℝ) + 1) := by
      refine ⟨ht.1, ?_⟩
      have hceil : t - s ≤ (⌈t - s⌉₊ : ℝ) := Nat.le_ceil (t - s)
      linarith
    exact regularCylFlow_unique_slice hν hc hbu hs (hu ⌈t - s⌉₊) (hu N)
      ((hus ⌈t - s⌉₊).trans (hus N).symm) ht' ht
  have hw_s : w s = f := by
    rw [hw_eq 0 s ⟨le_rfl, by norm_num⟩, hus 0]
  have hreg : ∀ T : ℝ, s ≤ T → IsRegularCylFlow c ν tr.v s T w := by
    intro T hsT
    set N : ℕ := ⌈T - s⌉₊
    have hTN_le : T ≤ s + (N : ℝ) + 1 := by
      have hceil : T - s ≤ (N : ℝ) := Nat.le_ceil (T - s)
      linarith
    have hsub : Icc s T ⊆ Icc s (s + (N : ℝ) + 1) := Icc_subset_Icc_right hTN_le
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ((hu N).jointCont.mono (prod_mono hsub Subset.rfl)).congr ?_
      intro z hz
      exact congrFun (hw_eq N z.1 (hsub hz.1)) z.2
    · intro σ hσ
      rw [hw_eq N σ (hsub hσ)]
      exact (hu N).slice σ (hsub hσ)
    · intro N'
      obtain ⟨C, hC⟩ := (hu N).decay N'
      refine ⟨C, fun σ hσ x => ?_⟩
      rw [hw_eq N σ (hsub hσ)]
      exact hC σ (hsub hσ) x
    · intro σ hσ x
      rw [hw_eq N σ (hsub hσ)]
      have hpde := ((hu N).pde σ (hsub hσ) x).mono hsub
      refine hpde.congr (fun r hr => congrFun (hw_eq N r (hsub hr)) x) ?_
      exact congrFun (hw_eq N σ (hsub hσ)) x
  refine ⟨w, ?_, hw_s, hreg⟩
  have hm0 : 0 ≤ m := by linarith
  have hm1 : 1 < m := by linarith
  have hw_mem : ∀ t : ℝ, s ≤ t → MemLp (w t) 2 (B0579.cellMeasure c m) :=
    fun t hst => cylRegularMem ν c m s t tr.v w hc hm0 (hreg t hst) t ⟨hst, le_rfl⟩
  refine ⟨Filter.EventuallyEq.of_eq hw_s, hw_mem, strongCont_of_regular hc hm0 hreg, ?_, ?_, ?_⟩
  · intro φ hφ r hsr
    have hr0 : 0 ≤ r := le_trans hs hsr
    obtain ⟨V, _, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu hr0
    obtain ⟨B1, hB1⟩ := lztCylBounded hc (hφ.pd 0)
    obtain ⟨B2, hB2⟩ := lztCylBounded hc (hφ.pd 1)
    obtain ⟨B3, hB3⟩ := lztCylBounded hc ((hφ.pd 0).pd 0)
    obtain ⟨B4, hB4⟩ := lztCylBounded hc ((hφ.pd 1).pd 1)
    have hvr : ContDiff ℝ ∞ (tr.v r) := by
      have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (s := univ) (fun z _ => ⟨mem_Ici.2 hr0, mem_univ z⟩)
      exact contDiffOn_univ.1 h
    have hv0_cont : Continuous (fun x => tr.v r x 0) :=
      (PiLp.continuous_apply 2 _ 0).comp hvr.continuous
    have hv1_cont : Continuous (fun x => tr.v r x 1) :=
      (PiLp.continuous_apply 2 _ 1).comp hvr.continuous
    have hlap_cont : Continuous (lapP φ) :=
      ((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous
    have hg_cont : Continuous (fun x => ν * lapP φ x +
        (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)) :=
      (continuous_const.mul hlap_cont).add
        ((hv0_cont.mul (hφ.pd 0).continuous).add (hv1_cont.mul (hφ.pd 1).continuous))
    have hg_bd : ∀ x : B0579.Plane,
        |ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)| ≤
          |ν| * (|B3| + |B4|) + |V| * (|B1| + |B2|) := by
      intro x
      have hv0 := (hV r ⟨hr0, le_rfl⟩ x 0).1.trans (le_abs_self V)
      have hv1 := (hV r ⟨hr0, le_rfl⟩ x 1).1.trans (le_abs_self V)
      have hp1 := (hB1 x).trans (le_abs_self B1)
      have hp2 := (hB2 x).trans (le_abs_self B2)
      have hp3 := (hB3 x).trans (le_abs_self B3)
      have hp4 := (hB4 x).trans (le_abs_self B4)
      have hL : |lapP φ x| ≤ |B3| + |B4| := by
        unfold lapP
        exact (abs_add_le _ _).trans (add_le_add hp3 hp4)
      have t1 : |ν * lapP φ x| ≤ |ν| * (|B3| + |B4|) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      have t2 : |tr.v r x 0 * B0579.pd 0 φ x| ≤ |V| * |B1| := by
        rw [abs_mul]; exact mul_le_mul hv0 hp1 (abs_nonneg _) (abs_nonneg _)
      have t3 : |tr.v r x 1 * B0579.pd 1 φ x| ≤ |V| * |B2| := by
        rw [abs_mul]; exact mul_le_mul hv1 hp2 (abs_nonneg _) (abs_nonneg _)
      have a1 := abs_add_le (ν * lapP φ x)
        (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)
      have a2 := abs_add_le (tr.v r x 0 * B0579.pd 0 φ x) (tr.v r x 1 * B0579.pd 1 φ x)
      linarith
    have hg_mem := cylLhs_memLp_neg hm1 c hg_cont hg_bd
    exact cylLhs_integrableOn (w r) _ (hw_mem r hsr) hg_mem
  · intro φ hφ t₁ hst₁
    have ht10 : 0 ≤ t₁ := le_trans hs hst₁
    obtain ⟨V, _, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu ht10
    have hM : ∃ M : ℝ, ∀ r ∈ Icc s t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M :=
      ⟨2 * V, fun r hr x => by linarith [(hV r ⟨le_trans hs hr.1, hr.2⟩ x 0).1,
        (hV r ⟨le_trans hs hr.1, hr.2⟩ x 1).1]⟩
    have hI := (rtd_of_regular hc tr hs (hreg t₁ hst₁) hst₁ le_rfl
      (cylEtaTest_const hc hφ) hM).1
    have hfun : (fun r => ∫ x in B0579.cell c, w r x *
        (deriv (fun _ : ℝ => φ x) r + ν * lapP φ x +
          (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x))) =
        fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (w r) r φ x := by
      funext r
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [deriv_const r (φ x), zero_add]
      rfl
    rwa [hfun] at hI
  · intro φ hφ t₁ hst₁
    have ht10 : 0 ≤ t₁ := le_trans hs hst₁
    obtain ⟨V, _, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu ht10
    have hM : ∃ M : ℝ, ∀ r ∈ Icc s t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M :=
      ⟨2 * V, fun r hr x => by linarith [(hV r ⟨le_trans hs hr.1, hr.2⟩ x 0).1,
        (hV r ⟨le_trans hs hr.1, hr.2⟩ x 1).1]⟩
    have hEq := (rtd_of_regular hc tr hs (hreg t₁ hst₁) hst₁ le_rfl
      (cylEtaTest_const hc hφ) hM).2
    rw [hw_s] at hEq
    have hRhs : (∫ r in s..t₁, ∫ x in B0579.cell c, w r x *
        (deriv (fun _ : ℝ => φ x) r + ν * lapP φ x +
          (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x))) =
        ∫ r in s..t₁, ∫ x in B0579.cell c, cylFreeIntegrand tr (w r) r φ x := by
      refine intervalIntegral.integral_congr fun r _ => ?_
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [deriv_const r (φ x), zero_add]
      rfl
    rw [hRhs] at hEq
    linarith

end UnforcedLeray.Short.IIb

end
