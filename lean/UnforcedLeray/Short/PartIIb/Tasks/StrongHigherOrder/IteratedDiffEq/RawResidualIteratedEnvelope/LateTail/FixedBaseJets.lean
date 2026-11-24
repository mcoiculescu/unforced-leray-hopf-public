import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.LateTail.HeatJetAll
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.LateTail.WtdProfCalc
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_R06
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanDatumRemainderMixedFixed
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanSourceFarBoundFixed
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanSourceNearDiffBoundFixed
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanSourceRemainderHeatStep

/-!
# Fixed-threshold all-order `WtdProfJet` bounds for all residual/remainder blocks (`s ≥ 1`)

Source of record: `the November 2 reference manuscript`, lines 427-459, 499-526,
1243-1285, 1310-1325, 1656-1680, 2548-2551.

At a single viscosity threshold `ν₀ > 0` independent of derivative order `m`, weight `w`, and
rapid-decay exponent `K`, establishes:
1. `RapidProf` (`∀ m w K, WtdProfJet m w (-K)`) for `fluctFam`, `presFam`, `stressFam`, and hence
   all five fluctuation/pressure/`A₂` residual blocks (`fluctB1`, `fluctB3`, `fluctA1`,
   `Jet.B2.fluctB2`, `coefA2Fam`);
2. `EvRapidProf` (`∀ m w K, ∃ M₀, ∀ M ≥ M₀, WtdProfJet m w (-K)`) for `remFam` and hence all four
   mean remainder blocks (`remB1`, `remB3`, `remA1`, `BlockB2Sub.remB2`);
3. `exists_late_rem_total_jet` and `late_lift_decomp_off_axis` for the combined meridional
   remainder profile `r_rem_total p M`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.FarDecaySub
open UnforcedLeray.Short.PartIIIb.Concrete.EarlyJet2Sub
open UnforcedLeray.Short.PartIIIb.Concrete.LateHeatDecomp2Sub

namespace UnforcedLeray.Short.IIb.RawResidualIteratedLateTailAux

/-! ### 1. Unconditional fixed-parameter mean remainder theorem and pullback helpers -/

/-- Unconditional proof of `PartI.TrainMeanRemFixed` assembled from `PartII-a:R06/1..4`. -/
theorem trainMeanRemFixed : PartI.TrainMeanRemFixed :=
  trainMeanRemFixed_of
    (trainMeanRemMixedFixed_of meanDatumRemainderMixedFixed meanSourceFarBoundFixed
      meanSourceNearDiffBoundFixed meanSourceRemainderHeatStep)

/-- Continuous linear map `ProfilePoint →L[ℝ] (ℝ × ℝ)` sending `x = (q, (η, s))` to `(s, η)`. -/
def πProf1D : ProfilePoint →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

@[simp]
theorem πProf1D_apply (x : ProfilePoint) : πProf1D x = (x.2.2, x.2.1) := rfl

theorem norm_πProf1D_le_one : ‖πProf1D‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul]
  change max ‖u.2.2‖ ‖u.2.1‖ ≤ max ‖u.1‖ (max ‖u.2.1‖ ‖u.2.2‖)
  exact (le_of_eq (max_comm _ _)).trans (le_max_right _ _)

theorem pullback_2d_smooth_and_jet {F : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun y : ℝ × Plane => F y.1 y.2) (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ ∞ (trainProfile F) ageDomain ∧
      ∀ (x : ProfilePoint) (j : ℕ),
        ‖iteratedFDeriv ℝ j (trainProfile F) x‖ =
          ‖iteratedFDeriv ℝ j (fun y : ℝ × Plane => F y.1 y.2) (x.2.2, (x.1, x.2.1))‖ := by
  have heq : trainProfile F = (fun y : ℝ × Plane => F y.1 y.2) ∘ chartSwapLIE.symm := rfl
  refine ⟨hf.comp chartSwapLIE.symm.contDiff.contDiffOn fun x hx => ⟨hx, trivial⟩, fun x j => ?_⟩
  rw [heq]
  exact chartSwapLIE.symm.norm_iteratedFDeriv_comp_right (fun y : ℝ × Plane => F y.1 y.2) x j

theorem pullback_1d_smooth_and_jet {H : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => H y.1 y.2) (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ ∞ (trainProfile fun s z => H s z.2) ageDomain ∧
      ∀ (x : ProfilePoint), 0 < x.2.2 → ∀ j : ℕ,
        ‖iteratedFDeriv ℝ j (trainProfile fun s z => H s z.2) x‖ ≤
          ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => H y.1 y.2) (x.2.2, x.2.1)‖ := by
  set U : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hpre : πProf1D ⁻¹' U = ageDomain := by
    ext x
    simp [U, ageDomain]
  let g : ℝ × ℝ → ℝ := fun y => H y.1 y.2
  have heq : (trainProfile fun s z => H s z.2) = g ∘ πProf1D := rfl
  refine ⟨hg.comp πProf1D.contDiff.contDiffOn fun x hx => ⟨hx, trivial⟩, fun x hx0 j => ?_⟩
  have hxU : πProf1D x ∈ U := ⟨hx0, trivial⟩
  have hxPre : x ∈ πProf1D ⁻¹' U := hxU
  have hOpenPre : IsOpen (πProf1D ⁻¹' U) := hU.preimage πProf1D.continuous
  have hid : iteratedFDeriv ℝ j (g ∘ πProf1D) x =
      (iteratedFDeriv ℝ j g (πProf1D x)).compContinuousLinearMap fun _ => πProf1D := by
    rw [← iteratedFDerivWithin_of_isOpen j hOpenPre hxPre,
      πProf1D.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hOpenPre.uniqueDiffOn hxU
        (by exact_mod_cast le_top),
      iteratedFDerivWithin_of_isOpen j hU hxU]
  rw [heq, hid]
  have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j g (πProf1D x)) (fun _ => πProf1D)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
  have hpow1 : ‖πProf1D‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) norm_πProf1D_le_one
  exact hcomp.trans (mul_le_of_le_one_right (norm_nonneg _) hpow1)

theorem abs_hmean_le_of_forall {c : ℝ} (hc : 0 < c) {F : Plane → ℝ} {η M : ℝ} (_hM0 : 0 ≤ M)
    (hF : ∀ q : ℝ, |F (q, η)| ≤ M) :
    |PartI.hmean c F η| ≤ M := by
  have hbd : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖F (q, η)‖ ≤ M := fun q _ => by
    rw [Real.norm_eq_abs]; exact hF q
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (-c / 2) (c / 2)) measure_Ioc_lt_top hbd
  rw [Real.volume_real_Ioc_of_le (by linarith)] at hint
  have hint' : ‖∫ q in Ioc (-c / 2) (c / 2), F (q, η)‖ ≤ M * c := by
    calc ‖∫ q in Ioc (-c / 2) (c / 2), F (q, η)‖
        ≤ M * (c / 2 - -c / 2) := hint
      _ = M * c := by ring
  rw [ ← Real.norm_eq_abs]
  unfold PartI.hmean
  rw [smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), F (q, η)‖
      ≤ c⁻¹ * (M * c) := mul_le_mul_of_nonneg_left hint' (inv_nonneg.2 hc.le)
    _ = M := by field_simp [hc.ne']

/-! ### 2. Abstract jet-growth classes (`RapidProf`, `TempProf`, `EvRapidProf`, `UnifTempProf`) -/

/-- All-order, all-weight, all-rapid-decay profile on `1 ≤ x.2.2`. -/
def RapidProf (f : ProfilePoint → ℝ) : Prop :=
  ∀ m w K : ℕ, WtdProfJet m w (-(K : ℝ)) f

/-- All-order, all-weight profile with polynomial-in-`s` growth on `1 ≤ x.2.2`. -/
def TempProf (f : ProfilePoint → ℝ) : Prop :=
  ∀ m w : ℕ, ∃ A : ℕ, WtdProfJet m w (A : ℝ) f

/-- Sequence of profiles that eventually (in `M`) achieves any `(m, w, K)` rapid decay. -/
def EvRapidProf (F : ℕ → ProfilePoint → ℝ) : Prop :=
  ∀ m w K : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → WtdProfJet m w (-(K : ℝ)) (F M)

/-- Sequence of profiles with `(m, w)` polynomial-in-`s` exponent independent of `M`. -/
def UnifTempProf (F : ℕ → ProfilePoint → ℝ) : Prop :=
  ∀ m w : ℕ, ∃ A : ℕ, ∀ M : ℕ, WtdProfJet m w (A : ℝ) (F M)

theorem eqOn_dirDeriv_ageDomain (v : ProfilePoint) {f g : ProfilePoint → ℝ}
    (h : EqOn f g ageDomain) :
    EqOn (fun x => fderiv ℝ f x v) (fun x => fderiv ℝ g x v) ageDomain := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] g :=
    Filter.eventuallyEq_of_mem (B0185.isOpen_ageDomain.mem_nhds hx) fun y hy => h hy
  simp only [hev.fderiv_eq]

theorem RapidProf.congr {f g : ProfilePoint → ℝ} (hf : RapidProf f) (hfg : EqOn f g ageDomain) :
    RapidProf g :=
  fun m w K => (hf m w K).congr hfg

theorem RapidProf.add {f g : ProfilePoint → ℝ} (hf : RapidProf f) (hg : RapidProf g) :
    RapidProf (fun x => f x + g x) :=
  fun m w K => (hf m w K).add (hg m w K)

theorem RapidProf.sub {f g : ProfilePoint → ℝ} (hf : RapidProf f) (hg : RapidProf g) :
    RapidProf (fun x => f x - g x) :=
  fun m w K => (hf m w K).sub (hg m w K)

theorem RapidProf.neg {f : ProfilePoint → ℝ} (hf : RapidProf f) :
    RapidProf (fun x => -f x) :=
  fun m w K => (hf m w K).neg

theorem RapidProf.const_mul (c : ℝ) {f : ProfilePoint → ℝ} (hf : RapidProf f) :
    RapidProf (fun x => c * f x) :=
  fun m w K => (hf m w K).const_mul c

theorem RapidProf.partialQ {f : ProfilePoint → ℝ} (hf : RapidProf f) :
    RapidProf (UnforcedLeray.B0184.partialQ f) :=
  fun m w K => (hf (m + 1) w K).partialQ

theorem RapidProf.partialEta {f : ProfilePoint → ℝ} (hf : RapidProf f) :
    RapidProf (UnforcedLeray.B0184.partialEta f) :=
  fun m w K => (hf (m + 1) w K).partialEta

theorem RapidProf.partialAge {f : ProfilePoint → ℝ} (hf : RapidProf f) :
    RapidProf (UnforcedLeray.B0184.partialAge f) :=
  fun m w K => (hf (m + 1) w K).partialAge

theorem RapidProf.ageOp {f : ProfilePoint → ℝ} (hf : RapidProf f) :
    RapidProf (ageOperator f) := by
  intro m w K
  have h := (hf (m + 1) (w + 1) (K + 1)).ageOp
  have hexp : -(((K + 1 : ℕ) : ℝ)) + 1 = -(K : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem RapidProf.ageShift (r : ℝ) {f : ProfilePoint → ℝ} (hf : RapidProf f) :
    RapidProf (UnforcedLeray.B0188.ageShift r f) := by
  intro m w K
  have h := (hf (m + 1) (w + 1) (K + 1)).ageShift r
  have hexp : -(((K + 1 : ℕ) : ℝ)) + 1 = -(K : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem RapidProf.toTemp {f : ProfilePoint → ℝ} (hf : RapidProf f) : TempProf f :=
  fun m w => ⟨0, (hf m w 0).mono_alpha (by norm_num)⟩

theorem TempProf.congr {f g : ProfilePoint → ℝ} (hf : TempProf f) (hfg : EqOn f g ageDomain) :
    TempProf g :=
  fun m w => let ⟨A, hA⟩ := hf m w; ⟨A, hA.congr hfg⟩

theorem TempProf.add {f g : ProfilePoint → ℝ} (hf : TempProf f) (hg : TempProf g) :
    TempProf (fun x => f x + g x) := by
  intro m w
  obtain ⟨A₁, h₁⟩ := hf m w
  obtain ⟨A₂, h₂⟩ := hg m w
  exact ⟨max A₁ A₂,
    (h₁.mono_alpha (Nat.cast_le.2 (le_max_left A₁ A₂))).add
      (h₂.mono_alpha (Nat.cast_le.2 (le_max_right A₁ A₂)))⟩

theorem TempProf.neg {f : ProfilePoint → ℝ} (hf : TempProf f) :
    TempProf (fun x => -f x) :=
  fun m w => let ⟨A, hA⟩ := hf m w; ⟨A, hA.neg⟩

theorem TempProf.sub {f g : ProfilePoint → ℝ} (hf : TempProf f) (hg : TempProf g) :
    TempProf (fun x => f x - g x) := by
  intro m w
  obtain ⟨A₁, h₁⟩ := hf m w
  obtain ⟨A₂, h₂⟩ := hg m w
  exact ⟨max A₁ A₂,
    (h₁.mono_alpha (Nat.cast_le.2 (le_max_left A₁ A₂))).sub
      (h₂.mono_alpha (Nat.cast_le.2 (le_max_right A₁ A₂)))⟩

theorem TempProf.partialEta {f : ProfilePoint → ℝ} (hf : TempProf f) :
    TempProf (UnforcedLeray.B0184.partialEta f) :=
  fun m w => let ⟨A, hA⟩ := hf (m + 1) w; ⟨A, hA.partialEta⟩

theorem TempProf.ageOp {f : ProfilePoint → ℝ} (hf : TempProf f) :
    TempProf (ageOperator f) := by
  intro m w
  obtain ⟨A, hA⟩ := hf (m + 1) (w + 1)
  refine ⟨A + 1, ?_⟩
  have h := hA.ageOp
  have hexp : (A : ℝ) + 1 = ((A + 1 : ℕ) : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem TempProf.ageShift (r : ℝ) {f : ProfilePoint → ℝ} (hf : TempProf f) :
    TempProf (UnforcedLeray.B0188.ageShift r f) := by
  intro m w
  obtain ⟨A, hA⟩ := hf (m + 1) (w + 1)
  refine ⟨A + 1, ?_⟩
  have h := hA.ageShift r
  have hexp : (A : ℝ) + 1 = ((A + 1 : ℕ) : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem RapidProf.mul_temp {f g : ProfilePoint → ℝ} (hf : RapidProf f) (hg : TempProf g) :
    RapidProf (fun x => f x * g x) := by
  intro m w K
  obtain ⟨A, hgA⟩ := hg m 0
  have h := (hf m w (K + A)).mul hgA
  have hexp : -(((K + A : ℕ) : ℝ)) + (A : ℝ) = -(K : ℝ) := by push_cast; ring
  rw [Nat.add_zero, hexp] at h
  exact h

theorem TempProf.mul_rapid {f g : ProfilePoint → ℝ} (hf : TempProf f) (hg : RapidProf g) :
    RapidProf (fun x => f x * g x) := by
  intro m w K
  obtain ⟨A, hfA⟩ := hf m 0
  have h := hfA.mul (hg m w (K + A))
  have hexp : (A : ℝ) + -(((K + A : ℕ) : ℝ)) = -(K : ℝ) := by push_cast; ring
  rw [Nat.zero_add, hexp] at h
  exact h

theorem TempProf.toUnif {f : ProfilePoint → ℝ} (hf : TempProf f) :
    UnifTempProf (fun _ => f) :=
  fun m w => let ⟨A, hA⟩ := hf m w; ⟨A, fun _ => hA⟩

theorem UnifTempProf.sub {F G : ℕ → ProfilePoint → ℝ}
    (hF : UnifTempProf F) (hG : UnifTempProf G) :
    UnifTempProf (fun M x => F M x - G M x) := by
  intro m w
  obtain ⟨A₁, h₁⟩ := hF m w
  obtain ⟨A₂, h₂⟩ := hG m w
  exact ⟨max A₁ A₂, fun M =>
    ((h₁ M).mono_alpha (Nat.cast_le.2 (le_max_left A₁ A₂))).sub
      ((h₂ M).mono_alpha (Nat.cast_le.2 (le_max_right A₁ A₂)))⟩

theorem UnifTempProf.neg {F : ℕ → ProfilePoint → ℝ} (hF : UnifTempProf F) :
    UnifTempProf (fun M x => -F M x) :=
  fun m w => let ⟨A, hA⟩ := hF m w; ⟨A, fun M => (hA M).neg⟩

theorem UnifTempProf.partialEta {F : ℕ → ProfilePoint → ℝ} (hF : UnifTempProf F) :
    UnifTempProf (fun M => UnforcedLeray.B0184.partialEta (F M)) :=
  fun m w => let ⟨A, hA⟩ := hF (m + 1) w; ⟨A, fun M => (hA M).partialEta⟩

theorem UnifTempProf.ageOp {F : ℕ → ProfilePoint → ℝ} (hF : UnifTempProf F) :
    UnifTempProf (fun M => ageOperator (F M)) := by
  intro m w
  obtain ⟨A, hA⟩ := hF (m + 1) (w + 1)
  refine ⟨A + 1, fun M => ?_⟩
  have h := (hA M).ageOp
  have hexp : (A : ℝ) + 1 = ((A + 1 : ℕ) : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem UnifTempProf.ageShift (r : ℝ) {F : ℕ → ProfilePoint → ℝ} (hF : UnifTempProf F) :
    UnifTempProf (fun M => UnforcedLeray.B0188.ageShift r (F M)) := by
  intro m w
  obtain ⟨A, hA⟩ := hF (m + 1) (w + 1)
  refine ⟨A + 1, fun M => ?_⟩
  have h := (hA M).ageShift r
  have hexp : (A : ℝ) + 1 = ((A + 1 : ℕ) : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem EvRapidProf.congr {F G : ℕ → ProfilePoint → ℝ}
    (hF : EvRapidProf F) (hFG : ∀ M, EqOn (F M) (G M) ageDomain) :
    EvRapidProf G :=
  fun m w K => let ⟨M₀, hM₀⟩ := hF m w K; ⟨M₀, fun M hM => (hM₀ M hM).congr (hFG M)⟩

theorem EvRapidProf.add {F G : ℕ → ProfilePoint → ℝ}
    (hF : EvRapidProf F) (hG : EvRapidProf G) :
    EvRapidProf (fun M x => F M x + G M x) := by
  intro m w K
  obtain ⟨M₁, h₁⟩ := hF m w K
  obtain ⟨M₂, h₂⟩ := hG m w K
  exact ⟨max M₁ M₂, fun M hM =>
    (h₁ M ((le_max_left M₁ M₂).trans hM)).add (h₂ M ((le_max_right M₁ M₂).trans hM))⟩

theorem EvRapidProf.neg {F : ℕ → ProfilePoint → ℝ} (hF : EvRapidProf F) :
    EvRapidProf (fun M x => -F M x) :=
  fun m w K => let ⟨M₀, hM₀⟩ := hF m w K; ⟨M₀, fun M hM => (hM₀ M hM).neg⟩

theorem EvRapidProf.sub {F G : ℕ → ProfilePoint → ℝ}
    (hF : EvRapidProf F) (hG : EvRapidProf G) :
    EvRapidProf (fun M x => F M x - G M x) := by
  intro m w K
  obtain ⟨M₁, h₁⟩ := hF m w K
  obtain ⟨M₂, h₂⟩ := hG m w K
  exact ⟨max M₁ M₂, fun M hM =>
    (h₁ M ((le_max_left M₁ M₂).trans hM)).sub (h₂ M ((le_max_right M₁ M₂).trans hM))⟩

theorem EvRapidProf.const_mul (c : ℝ) {F : ℕ → ProfilePoint → ℝ} (hF : EvRapidProf F) :
    EvRapidProf (fun M x => c * F M x) :=
  fun m w K => let ⟨M₀, hM₀⟩ := hF m w K; ⟨M₀, fun M hM => (hM₀ M hM).const_mul c⟩

theorem EvRapidProf.partialEta {F : ℕ → ProfilePoint → ℝ} (hF : EvRapidProf F) :
    EvRapidProf (fun M => UnforcedLeray.B0184.partialEta (F M)) :=
  fun m w K => let ⟨M₀, hM₀⟩ := hF (m + 1) w K; ⟨M₀, fun M hM => (hM₀ M hM).partialEta⟩

theorem EvRapidProf.ageOp {F : ℕ → ProfilePoint → ℝ} (hF : EvRapidProf F) :
    EvRapidProf (fun M => ageOperator (F M)) := by
  intro m w K
  obtain ⟨M₀, hM₀⟩ := hF (m + 1) (w + 1) (K + 1)
  refine ⟨M₀, fun M hM => ?_⟩
  have h := (hM₀ M hM).ageOp
  have hexp : -(((K + 1 : ℕ) : ℝ)) + 1 = -(K : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem EvRapidProf.ageShift (r : ℝ) {F : ℕ → ProfilePoint → ℝ} (hF : EvRapidProf F) :
    EvRapidProf (fun M => UnforcedLeray.B0188.ageShift r (F M)) := by
  intro m w K
  obtain ⟨M₀, hM₀⟩ := hF (m + 1) (w + 1) (K + 1)
  refine ⟨M₀, fun M hM => ?_⟩
  have h := (hM₀ M hM).ageShift r
  have hexp : -(((K + 1 : ℕ) : ℝ)) + 1 = -(K : ℝ) := by push_cast; ring
  rwa [hexp] at h

theorem UnifTempProf.mul_evRapid {F G : ℕ → ProfilePoint → ℝ}
    (hF : UnifTempProf F) (hG : EvRapidProf G) :
    EvRapidProf (fun M x => F M x * G M x) := by
  intro m w K
  obtain ⟨A, hFA⟩ := hF m 0
  obtain ⟨M₀, hGKA⟩ := hG m w (K + A)
  refine ⟨M₀, fun M hM => ?_⟩
  have h := (hFA M).mul (hGKA M hM)
  have hexp : (A : ℝ) + -(((K + A : ℕ) : ℝ)) = -(K : ℝ) := by push_cast; ring
  rw [Nat.zero_add, hexp] at h
  exact h

theorem EvRapidProf.mul_unifTemp {F G : ℕ → ProfilePoint → ℝ}
    (hF : EvRapidProf F) (hG : UnifTempProf G) :
    EvRapidProf (fun M x => F M x * G M x) := by
  intro m w K
  obtain ⟨A, hGA⟩ := hG m 0
  obtain ⟨M₀, hFKA⟩ := hF m w (K + A)
  refine ⟨M₀, fun M hM => ?_⟩
  have h := (hFKA M hM).mul (hGA M)
  have hexp : -(((K + A : ℕ) : ℝ)) + (A : ℝ) = -(K : ℝ) := by push_cast; ring
  rw [Nat.add_zero, hexp] at h
  exact h

theorem EvRapidProf.mul_evRapid {F G : ℕ → ProfilePoint → ℝ}
    (hF : EvRapidProf F) (hG : EvRapidProf G) :
    EvRapidProf (fun M x => F M x * G M x) := by
  intro m w K
  obtain ⟨M₁, h₁⟩ := hF m w K
  obtain ⟨M₂, h₂⟩ := hG m 0 0
  refine ⟨max M₁ M₂, fun M hM => ?_⟩
  have h := (h₁ M ((le_max_left M₁ M₂).trans hM)).mul (h₂ M ((le_max_right M₁ M₂).trans hM))
  have hexp : -(K : ℝ) + -((0 : ℕ) : ℝ) = -(K : ℝ) := by push_cast; ring
  rw [Nat.add_zero, hexp] at h
  exact h

/-! ### 3. Regime 2 far-`η` tail bounds and base-family `RapidProf` / `EvRapidProf` bounds -/

/-- On `1 ≤ x.2.2 ≤ |x.2.1|`, `heatSumFam N ν c tr` has rapid decay `(1 + |η|)^W |heatSumFam| ≤ B s^{-K}`
for every `(N, W, K)` and every `0 < ν ≤ 1`. -/
theorem heatSumFam_far_eta_bound {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (c : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (N W K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 → x.2.2 ≤ |x.2.1| →
      (1 + |x.2.1|) ^ W * |heatSumFam N ν c tr x| ≤ B * x.2.2 ^ (-(K : ℝ)) := by
  have h_term : ∀ j : ℕ, ∃ Bj : ℝ, 0 ≤ Bj ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 → x.2.2 ≤ |x.2.1| →
      (1 + |x.2.1|) ^ W * |meanCoeff tr j * lhP ν (2 * j) x| ≤ Bj * x.2.2 ^ (-(K : ℝ)) := by
    intro j
    obtain ⟨C, hC0, hC⟩ := lhBound1D (W + K) (2 * j)
    set Bj : ℝ := |meanCoeff tr j| * C * ν ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2)
    refine ⟨Bj, by unfold Bj; positivity, fun x hx1 hη => ?_⟩
    have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
    have hU0 : 0 ≤ 1 + x.2.1 ^ 2 / x.2.2 := by positivity
    have h1_le_U : 1 + |x.2.1| ≤ 1 + x.2.1 ^ 2 / x.2.2 := by
      have hsq : |x.2.1| * x.2.2 ≤ x.2.1 ^ 2 := by
        have := mul_le_mul_of_nonneg_left hη (abs_nonneg x.2.1)
        linarith [sq_abs x.2.1]
      have hdiv : |x.2.1| ≤ x.2.1 ^ 2 / x.2.2 := (le_div_iff₀ hx0).2 hsq
      linarith
    have hs_le_U : x.2.2 ≤ 1 + x.2.1 ^ 2 / x.2.2 := by
      have hsq : x.2.2 * x.2.2 ≤ x.2.1 ^ 2 := by
        have h1 := mul_le_mul hη hη hx0.le (abs_nonneg x.2.1)
        linarith [sq_abs x.2.1]
      have hdiv : x.2.2 ≤ x.2.1 ^ 2 / x.2.2 := (le_div_iff₀ hx0).2 hsq
      linarith
    have hpow_le : (1 + |x.2.1|) ^ W * x.2.2 ^ K ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ (W + K) := by
      rw [pow_add]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1_le_U W)
        (pow_le_pow_left₀ hx0.le hs_le_U K) (pow_nonneg hx0.le K) (pow_nonneg hU0 W)
    have h_sK_inv : x.2.2 ^ K * x.2.2 ^ (-(K : ℝ)) = 1 := by
      rw [← Real.rpow_natCast x.2.2 K, ← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
    have h1D := hC ν hν0 hν1 x.2.2 hx1 x.2.1
    have hexp_eq : -((((2 * j : ℕ) : ℝ) + 1) / 2) = -(((2 * j : ℕ) : ℝ) + 1) / 2 := by ring
    have hrp_le : (ν * x.2.2) ^ (-((((2 * j : ℕ) : ℝ) + 1) / 2)) ≤
        ν ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2) := by
      rw [Real.mul_rpow hν0.le hx0.le, hexp_eq]
      have hs_le1 : x.2.2 ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1
          (by linarith [Nat.cast_nonneg (α := ℝ) (2 * j)])
      calc ν ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2) * x.2.2 ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2)
          ≤ ν ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2) * 1 :=
            mul_le_mul_of_nonneg_left hs_le1 (Real.rpow_nonneg hν0.le _)
        _ = ν ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2) := mul_one _
    rw [abs_mul, lhP_eq]
    calc (1 + |x.2.1|) ^ W * (|meanCoeff tr j| *
            |iteratedDeriv (2 * j) (heatKernel1 (ν * x.2.2)) x.2.1|)
        = |meanCoeff tr j| * (((1 + |x.2.1|) ^ W * x.2.2 ^ K) *
            |iteratedDeriv (2 * j) (heatKernel1 (ν * x.2.2)) x.2.1|) *
              x.2.2 ^ (-(K : ℝ)) := by
          calc (1 + |x.2.1|) ^ W * (|meanCoeff tr j| *
                  |iteratedDeriv (2 * j) (heatKernel1 (ν * x.2.2)) x.2.1|)
              = |meanCoeff tr j| * (1 + |x.2.1|) ^ W *
                  |iteratedDeriv (2 * j) (heatKernel1 (ν * x.2.2)) x.2.1| *
                  (x.2.2 ^ K * x.2.2 ^ (-(K : ℝ))) := by rw [h_sK_inv, mul_one]; ring
            _ = _ := by ring
      _ ≤ |meanCoeff tr j| * ((1 + x.2.1 ^ 2 / x.2.2) ^ (W + K) *
            |iteratedDeriv (2 * j) (heatKernel1 (ν * x.2.2)) x.2.1|) *
              x.2.2 ^ (-(K : ℝ)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpow_le (abs_nonneg _)) (abs_nonneg _))
            (Real.rpow_nonneg hx0.le _)
      _ ≤ |meanCoeff tr j| * (C * ν ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2)) *
            x.2.2 ^ (-(K : ℝ)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (h1D.trans (mul_le_mul_of_nonneg_left hrp_le hC0)) (abs_nonneg _))
            (Real.rpow_nonneg hx0.le _)
      _ = Bj * x.2.2 ^ (-(K : ℝ)) := by unfold Bj; ring
  choose B_fn hB_fn using h_term
  refine ⟨∑ j ∈ Finset.range (N + 1), B_fn j, Finset.sum_nonneg fun j _ => (hB_fn j).1,
    fun x hx1 hη => ?_⟩
  unfold heatSumFam heatTermFam
  have habs : |∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) x| ≤
      ∑ j ∈ Finset.range (N + 1), |meanCoeff tr j * lhP ν (2 * j) x| :=
    Finset.abs_sum_le_sum_abs _ _
  calc (1 + |x.2.1|) ^ W * |∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) x|
      ≤ (1 + |x.2.1|) ^ W * ∑ j ∈ Finset.range (N + 1), |meanCoeff tr j * lhP ν (2 * j) x| :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = ∑ j ∈ Finset.range (N + 1), (1 + |x.2.1|) ^ W * |meanCoeff tr j * lhP ν (2 * j) x| :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), B_fn j * x.2.2 ^ (-(K : ℝ)) :=
        Finset.sum_le_sum fun j _ => (hB_fn j).2 x hx1 hη
    _ = (∑ j ∈ Finset.range (N + 1), B_fn j) * x.2.2 ^ (-(K : ℝ)) :=
        (Finset.sum_mul _ _ _).symm

/-- Single-threshold bundle of `RapidProf` / `EvRapidProf` for all base families at `ρ = 2`. -/
theorem exists_base_family_jets :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (PartI.trainPeriod 2 ν)), IsBUCTrain tr →
          let c := PartI.trainPeriod 2 ν
          RapidProf (Jet.fluctFam ν c tr) ∧
          RapidProf (Jet.presFam ν c tr) ∧
          RapidProf (Jet.A2.stressFam ν c tr) ∧
          EvRapidProf (fun M => remFam M ν c tr) := by
  have hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof
      (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
      (PartI.overlap_mean_decay_of PartI.overlapHighNormUniform_proof
        (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
        PartI.overlap_mean_primitive PartI.overlap_mean_duhamel_split)
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv (PartI.train_vorticity_gaussian_tail hOv)
  have hρ2 : (1 : ℝ) / 2 < 2 := by norm_num
  obtain ⟨b_T, C₀_T, C'_T, hb_T, hC₀_T, hC'_T, C₁_T, N₁_T, ν_tail, hC₁_T, hν_tail, hTail⟩ :=
    hTails.2.1 2 hρ2 0 0
  obtain ⟨ν_fl, hν_fl, hFluctFix⟩ := trainFluctFixed 2 hρ2
  obtain ⟨ν_pr, hν_pr, hPressFix⟩ := trainPressureFixed 2 hρ2
  obtain ⟨ν_vp, hν_vp, hVPFix⟩ := trainVelPressAgeJetFixed 2 hρ2
  obtain ⟨ν_sw, hν_sw, hStressW⟩ := meanStress_weighted_zero_fixed 2 hρ2
  obtain ⟨ν_rm, hν_rm, hRemFix⟩ := trainMeanRemFixed 2 hρ2
  let ν₀ : ℝ := min (min (min ν_tail ν_fl) (min ν_pr ν_vp)) (min (min ν_sw ν_rm) (1 / 2))
  have hν₀_pos : 0 < ν₀ :=
    lt_min
      (lt_min (lt_min hν_tail hν_fl) (lt_min hν_pr hν_vp))
      (lt_min (lt_min hν_sw hν_rm) (by norm_num))
  have hν₀_le1 : ν₀ ≤ 1 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  refine ⟨ν₀, hν₀_pos, hν₀_le1, fun ν hν hν_le tr htr => ?_⟩
  have hν_tail_le : ν ≤ ν_tail :=
    hν_le.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hν_fl_le : ν ≤ ν_fl :=
    hν_le.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hν_pr_le : ν ≤ ν_pr :=
    hν_le.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hν_vp_le : ν ≤ ν_vp :=
    hν_le.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hν_sw_le : ν ≤ ν_sw :=
    hν_le.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hν_rm_le : ν ≤ ν_rm :=
    hν_le.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 :=
    hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := by linarith
  let c : ℝ := PartI.trainPeriod 2 ν
  have hc1 : 1 < c := by
    change 1 < PartI.trainPeriod 2 ν
    unfold PartI.trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by norm_num)
  have hc0 : 0 < c := zero_lt_one.trans hc1
  set A_reg : ℝ := 4 + C'_T / ν
  have hA_reg : 0 < A_reg := by unfold A_reg; positivity
  -- Regime 2 (`|η| ≥ C'_T / ν + 2 + s`, `1 ≤ s`) weighted order-0 tail bound for `ψ`, `p`, `meanStream`:
  have hRegime2 : ∀ (W K : ℕ), ∃ B_tail : ℝ, 0 ≤ B_tail ∧
      ∀ (s η : ℝ), 1 ≤ s → C'_T / ν + 2 + s ≤ |η| →
        (∀ q : ℝ, (1 + |η|) ^ W * |tr.ψ s (q, η)| ≤ B_tail * s ^ (-(K : ℝ))) ∧
        (∀ q : ℝ, (1 + |η|) ^ W * |tr.p s (q, η)| ≤ B_tail * s ^ (-(K : ℝ))) ∧
        (1 + |η|) ^ W * |PartI.meanStream tr s η| ≤ B_tail * s ^ (-(K : ℝ)) := by
    intro W K
    set γ : ℝ := min (b_T / c) (b_T / (C₀_T + ν))
    have hγ : 0 < γ := by unfold γ; positivity
    obtain ⟨K_exp, hK_exp, hExp⟩ :=
      exp_neg_le_rpow_any γ hγ (-((W : ℝ) + (N₁_T : ℝ) + (K : ℝ)))
    set P_c : ℝ := C₁_T * (2 * (1 + c + ν⁻¹)) ^ N₁_T
    have hPc0 : 0 ≤ P_c := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      unfold P_c; positivity
    set B_tail : ℝ := 2 * A_reg ^ W * P_c * K_exp
    have hBt0 : 0 ≤ B_tail := by unfold B_tail; positivity
    refine ⟨B_tail, hBt0, fun s η hs hη => ?_⟩
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
    set l : ℝ := |η| - (C'_T / ν + 2)
    have hsl : s ≤ l := by dsimp [l]; linarith
    have hl1 : 1 ≤ l := hs.trans hsl
    have hl0 : 0 < l := lt_of_lt_of_le one_pos hl1
    have h_eta_le : 1 + |η| ≤ A_reg * l := by
      have heq : 1 + |η| = 3 + C'_T / ν + l := by dsimp [l]; ring
      have h1 : 3 + C'_T / ν ≤ (3 + C'_T / ν) * l :=
        le_mul_of_one_le_right (by positivity) hl1
      unfold A_reg
      linarith
    have h_wpow : (1 + |η|) ^ W ≤ A_reg ^ W * l ^ W := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h_eta_le W
    have h_poly : PartI.polyPS C₁_T N₁_T ν c s ≤ P_c * l ^ N₁_T := by
      unfold PartI.polyPS P_c
      rw [mul_assoc, ← mul_pow]
      have h1s : 1 + s ≤ 2 * l := by linarith
      have hcν0 : 0 ≤ 1 + c + ν⁻¹ := by have := inv_nonneg.2 hν.le; positivity
      have hbase : (1 + c + ν⁻¹) * (1 + s) ≤ 2 * (1 + c + ν⁻¹) * l := by nlinarith
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase N₁_T) hC₁_T.le
    have h_exp_sum : Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s))) ≤
        2 * Real.exp (-(γ * l)) := by
      have h1 : γ * l ≤ b_T * l / c := by
        calc γ * l ≤ (b_T / c) * l := mul_le_mul_of_nonneg_right (min_le_left _ _) hl0.le
          _ = b_T * l / c := by ring
      have h2 : γ * l ≤ b_T * l ^ 2 / (C₀_T + ν * s) := by
        have hden : C₀_T + ν * s ≤ (C₀_T + ν) * l := by nlinarith
        calc γ * l ≤ (b_T / (C₀_T + ν)) * l :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hl0.le
          _ = b_T * l ^ 2 / ((C₀_T + ν) * l) := by
              have hne : C₀_T + ν ≠ 0 := by positivity
              field_simp [hl0.ne']
          _ ≤ b_T * l ^ 2 / (C₀_T + ν * s) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      have he1 : Real.exp (-(b_T * l / c)) ≤ Real.exp (-(γ * l)) :=
        Real.exp_le_exp.2 (neg_le_neg h1)
      have he2 : Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s))) ≤ Real.exp (-(γ * l)) :=
        Real.exp_le_exp.2 (neg_le_neg h2)
      linarith
    have h_prod_le : (1 + |η|) ^ W *
        (PartI.polyPS C₁_T N₁_T ν c s *
          (Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s))))) ≤
        B_tail * s ^ (-(K : ℝ)) := by
      have hK_sl : PartI.polyPS C₁_T N₁_T ν c s *
          (Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s)))) ≤
          P_c * l ^ N₁_T * (2 * Real.exp (-(γ * l))) :=
        mul_le_mul h_poly h_exp_sum (by positivity) (mul_nonneg hPc0 (pow_nonneg hl0.le _))
      have h_l_rpow : l ^ (W + N₁_T) * Real.exp (-(γ * l)) ≤ K_exp * s ^ (-(K : ℝ)) := by
        have he := hExp l hl1
        have hmul := mul_le_mul_of_nonneg_left he (pow_nonneg hl0.le (W + N₁_T))
        have h_id : l ^ (W + N₁_T) * (K_exp * l ^ (-((W : ℝ) + (N₁_T : ℝ) + (K : ℝ)))) =
            K_exp * l ^ (-(K : ℝ)) := by
          rw [← Real.rpow_natCast l (W + N₁_T), mul_left_comm, ← Real.rpow_add hl0]
          congr 2
          push_cast
          ring
        have h_sl : l ^ (-(K : ℝ)) ≤ s ^ (-(K : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hs0 hsl (by linarith [Nat.cast_nonneg (α := ℝ) K])
        calc l ^ (W + N₁_T) * Real.exp (-(γ * l))
            ≤ K_exp * l ^ (-(K : ℝ)) := by rw [← h_id]; exact hmul
          _ ≤ K_exp * s ^ (-(K : ℝ)) := mul_le_mul_of_nonneg_left h_sl hK_exp.le
      calc (1 + |η|) ^ W *
            (PartI.polyPS C₁_T N₁_T ν c s *
              (Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s)))))
          ≤ (A_reg ^ W * l ^ W) * (P_c * l ^ N₁_T * (2 * Real.exp (-(γ * l)))) := by
            have hpoly0 : 0 ≤ PartI.polyPS C₁_T N₁_T ν c s := by
              unfold PartI.polyPS; have := inv_nonneg.2 hν.le; positivity
            exact mul_le_mul h_wpow hK_sl (mul_nonneg hpoly0 (by positivity)) (by positivity)
        _ = 2 * A_reg ^ W * P_c * (l ^ (W + N₁_T) * Real.exp (-(γ * l))) := by
            rw [pow_add]; ring
        _ ≤ 2 * A_reg ^ W * P_c * (K_exp * s ^ (-(K : ℝ))) :=
            mul_le_mul_of_nonneg_left h_l_rpow (by positivity)
        _ = B_tail * s ^ (-(K : ℝ)) := by unfold B_tail; ring
    have hq_psi_p : ∀ q : ℝ,
        |tr.ψ s (q, η)| ≤ PartI.polyPS C₁_T N₁_T ν c s *
            (Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s)))) ∧
        |tr.p s (q, η)| ≤ PartI.polyPS C₁_T N₁_T ν c s *
            (Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s)))) := by
      intro q
      have hz : C'_T / ν + 2 + l ≤ |((q, η) : Plane).2| := by
        change C'_T / ν + 2 + (|η| - (C'_T / ν + 2)) ≤ |η|
        linarith
      have ht := hTail s hs0.le ν hν hν_tail_le tr htr l hl0.le s hs0 le_rfl (q, η) hz
      have hψ := ht.1
      have hp := ht.2.2
      rw [PartI.PartI_T23.norm_ageJet_zero_zero, Real.norm_eq_abs] at hψ hp
      exact ⟨hψ, hp⟩
    have h_psi : ∀ q : ℝ, (1 + |η|) ^ W * |tr.ψ s (q, η)| ≤ B_tail * s ^ (-(K : ℝ)) :=
      fun q => (mul_le_mul_of_nonneg_left (hq_psi_p q).1 (by positivity)).trans h_prod_le
    have h_p : ∀ q : ℝ, (1 + |η|) ^ W * |tr.p s (q, η)| ≤ B_tail * s ^ (-(K : ℝ)) :=
      fun q => (mul_le_mul_of_nonneg_left (hq_psi_p q).2 (by positivity)).trans h_prod_le
    have h_mean : (1 + |η|) ^ W * |PartI.meanStream tr s η| ≤ B_tail * s ^ (-(K : ℝ)) := by
      set K_sl : ℝ := PartI.polyPS C₁_T N₁_T ν c s *
        (Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * s))))
      have hKsl0 : 0 ≤ K_sl := (abs_nonneg (tr.ψ s (0, η))).trans (hq_psi_p 0).1
      have hm_le : |PartI.meanStream tr s η| ≤ K_sl :=
        abs_hmean_le_of_forall hc0 hKsl0 fun q => (hq_psi_p q).1
      exact (mul_le_mul_of_nonneg_left hm_le (by positivity)).trans h_prod_le
    exact ⟨h_psi, h_p, h_mean⟩
  -- Regime 1 (`|η| ≤ C'_T / ν + 2 + s`, `1 ≤ s`) helper: `(1 + |η|)^W ≤ A_reg^W * s^W`
  have hRegime1_wpow : ∀ (W : ℕ) (s η : ℝ), 1 ≤ s → |η| ≤ C'_T / ν + 2 + s →
      (1 + |η|) ^ W ≤ A_reg ^ W * s ^ (W : ℝ) := by
    intro W s η hs hη
    have hs0 : 0 ≤ s := zero_le_one.trans hs
    have hbase : 1 + |η| ≤ A_reg * s := by
      have h1 : 3 + C'_T / ν ≤ (3 + C'_T / ν) * s :=
        le_mul_of_one_le_right (by positivity) hs
      unfold A_reg
      linarith
    rw [Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase W
  -- 1. `RapidProf (Jet.fluctFam ν c tr)`
  have hRapid_fluct : RapidProf (Jet.fluctFam ν c tr) := by
    intro m w K
    obtain ⟨hsm, hnorm⟩ := pullback_2d_smooth_and_jet
      (F := fun s z => tr.ψ s z - PartI.meanStream tr s z.2)
      (contDiffOn_streamFluct_meanStream hν hc0 tr htr)
    set W : ℕ := 2 ^ m * w
    obtain ⟨B_tail, hBt0, hR2⟩ := hRegime2 W K
    choose C_j κ_j hκ_j hbd_j using fun j : ℕ => hFluctFix ν hν hν_fl_le tr htr j
    choose K_j hKj_pos hExp_j using fun j : ℕ =>
      exp_neg_le_rpow_any (κ_j j) (hκ_j j) (-(K : ℝ))
    obtain ⟨K_0, hK0_pos, hExp_0⟩ :=
      exp_neg_le_rpow_any (κ_j 0) (hκ_j 0) (-((W : ℝ) + (K : ℝ)))
    set C₀ : ℝ := max (A_reg ^ W * |C_j 0| * K_0) (2 * B_tail)
    set C_u : ℝ := ∑ j ∈ Finset.range (m + 2), |C_j j| * K_j j
    refine wtdProfJet_of_zero_and_unweighted (C₀ := C₀) (C_u := C_u) hsm
      (le_max_of_le_right (mul_nonneg zero_le_two hBt0))
      (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hKj_pos j).le)
      (fun x hx1 => ?_) (fun x hx1 j hj => ?_)
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      rcases le_or_gt |x.2.1| (C'_T / ν + 2 + x.2.2) with hη | hη
      · have hw_le := hRegime1_wpow W x.2.2 x.2.1 hx1 hη
        have hu0 := hbd_j 0 (x.2.2, (x.1, x.2.1)) hx1
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hu0
        have hu0' : |Jet.fluctFam ν c tr x| ≤ |C_j 0| * Real.exp (-(κ_j 0 * x.2.2)) :=
          hu0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _))
        have hexp0 := hExp_0 x.2.2 hx1
        have hs_add : x.2.2 ^ (W : ℝ) * x.2.2 ^ (-((W : ℝ) + (K : ℝ))) = x.2.2 ^ (-(K : ℝ)) := by
          rw [← Real.rpow_add hx0]; congr 1; ring
        calc (1 + |x.2.1|) ^ W * |Jet.fluctFam ν c tr x|
            ≤ (A_reg ^ W * x.2.2 ^ (W : ℝ)) * (|C_j 0| * Real.exp (-(κ_j 0 * x.2.2))) :=
              mul_le_mul hw_le hu0' (abs_nonneg _) (by positivity)
          _ ≤ (A_reg ^ W * x.2.2 ^ (W : ℝ)) * (|C_j 0| * (K_0 * x.2.2 ^ (-((W : ℝ) + (K : ℝ))))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hexp0 (abs_nonneg _)) (by positivity)
          _ = (A_reg ^ W * |C_j 0| * K_0) *
                (x.2.2 ^ (W : ℝ) * x.2.2 ^ (-((W : ℝ) + (K : ℝ)))) := by ring
          _ = (A_reg ^ W * |C_j 0| * K_0) * x.2.2 ^ (-(K : ℝ)) := by rw [hs_add]
          _ ≤ C₀ * x.2.2 ^ (-(K : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
      · obtain ⟨h_psi, _, h_mean⟩ := hR2 x.2.2 x.2.1 hx1 hη.le
        have h_sub : |Jet.fluctFam ν c tr x| ≤ |tr.ψ x.2.2 (x.1, x.2.1)| +
            |PartI.meanStream tr x.2.2 x.2.1| := abs_sub _ _
        calc (1 + |x.2.1|) ^ W * |Jet.fluctFam ν c tr x|
            ≤ (1 + |x.2.1|) ^ W * |tr.ψ x.2.2 (x.1, x.2.1)| +
                (1 + |x.2.1|) ^ W * |PartI.meanStream tr x.2.2 x.2.1| := by
              rw [← mul_add]; exact mul_le_mul_of_nonneg_left h_sub (by positivity)
          _ ≤ B_tail * x.2.2 ^ (-(K : ℝ)) + B_tail * x.2.2 ^ (-(K : ℝ)) :=
              add_le_add (h_psi x.1) h_mean
          _ = (2 * B_tail) * x.2.2 ^ (-(K : ℝ)) := by ring
          _ ≤ C₀ * x.2.2 ^ (-(K : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      change ‖iteratedFDeriv ℝ j (trainProfile fun s z => tr.ψ s z - meanStream tr s z.2) x‖ ≤ _
      rw [hnorm x j]
      have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.2 (by omega)
      have hj_le : |C_j j| * K_j j ≤ C_u :=
        Finset.single_le_sum (fun i _ => mul_nonneg (abs_nonneg _) (hKj_pos i).le) hj_mem
      calc ‖iteratedFDeriv ℝ j (fun y : ℝ × Plane => tr.ψ y.1 y.2 - PartI.meanStream tr y.1 y.2.2)
              (x.2.2, (x.1, x.2.1))‖
          ≤ C_j j * Real.exp (-(κ_j j * x.2.2)) := hbd_j j (x.2.2, (x.1, x.2.1)) hx1
        _ ≤ |C_j j| * Real.exp (-(κ_j j * x.2.2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)
        _ ≤ |C_j j| * (K_j j * x.2.2 ^ (-(K : ℝ))) :=
            mul_le_mul_of_nonneg_left (hExp_j j x.2.2 hx1) (abs_nonneg _)
        _ = (|C_j j| * K_j j) * x.2.2 ^ (-(K : ℝ)) := by ring
        _ ≤ C_u * x.2.2 ^ (-(K : ℝ)) :=
            mul_le_mul_of_nonneg_right hj_le (Real.rpow_nonneg hx0.le _)
  -- 2. `RapidProf (Jet.presFam ν c tr)`
  have hRapid_pres : RapidProf (Jet.presFam ν c tr) := by
    intro m w K
    obtain ⟨hsm, hnorm⟩ := pullback_2d_smooth_and_jet
      (tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl))
    set W : ℕ := 2 ^ m * w
    obtain ⟨B_tail, hBt0, hR2⟩ := hRegime2 W K
    choose C_j κ_j hκ_j hbd_j using fun j : ℕ => hPressFix ν hν hν_pr_le tr htr j
    choose K_j hKj_pos hExp_j using fun j : ℕ =>
      exp_neg_le_rpow_any (κ_j j) (hκ_j j) (-(K : ℝ))
    obtain ⟨K_0, hK0_pos, hExp_0⟩ :=
      exp_neg_le_rpow_any (κ_j 0) (hκ_j 0) (-((W : ℝ) + (K : ℝ)))
    set C₀ : ℝ := max (A_reg ^ W * |C_j 0| * K_0) B_tail
    set C_u : ℝ := ∑ j ∈ Finset.range (m + 2), |C_j j| * K_j j
    refine wtdProfJet_of_zero_and_unweighted (C₀ := C₀) (C_u := C_u) hsm
      (le_max_of_le_right hBt0)
      (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hKj_pos j).le)
      (fun x hx1 => ?_) (fun x hx1 j hj => ?_)
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      rcases le_or_gt |x.2.1| (C'_T / ν + 2 + x.2.2) with hη | hη
      · have hw_le := hRegime1_wpow W x.2.2 x.2.1 hx1 hη
        have hu0 := hbd_j 0 (x.2.2, (x.1, x.2.1)) hx0
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hu0
        have hu0' : |Jet.presFam ν c tr x| ≤ |C_j 0| * Real.exp (-(κ_j 0 * x.2.2)) :=
          hu0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _))
        have hexp0 := hExp_0 x.2.2 hx1
        have hs_add : x.2.2 ^ (W : ℝ) * x.2.2 ^ (-((W : ℝ) + (K : ℝ))) = x.2.2 ^ (-(K : ℝ)) := by
          rw [← Real.rpow_add hx0]; congr 1; ring
        calc (1 + |x.2.1|) ^ W * |Jet.presFam ν c tr x|
            ≤ (A_reg ^ W * x.2.2 ^ (W : ℝ)) * (|C_j 0| * Real.exp (-(κ_j 0 * x.2.2))) :=
              mul_le_mul hw_le hu0' (abs_nonneg _) (by positivity)
          _ ≤ (A_reg ^ W * x.2.2 ^ (W : ℝ)) * (|C_j 0| * (K_0 * x.2.2 ^ (-((W : ℝ) + (K : ℝ))))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hexp0 (abs_nonneg _)) (by positivity)
          _ = (A_reg ^ W * |C_j 0| * K_0) *
                (x.2.2 ^ (W : ℝ) * x.2.2 ^ (-((W : ℝ) + (K : ℝ)))) := by ring
          _ = (A_reg ^ W * |C_j 0| * K_0) * x.2.2 ^ (-(K : ℝ)) := by rw [hs_add]
          _ ≤ C₀ * x.2.2 ^ (-(K : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
      · exact ((hR2 x.2.2 x.2.1 hx1 hη.le).2.1 x.1).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0.le _))
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      change ‖iteratedFDeriv ℝ j (trainProfile tr.p) x‖ ≤ _
      rw [hnorm x j]
      have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.2 (by omega)
      have hj_le : |C_j j| * K_j j ≤ C_u :=
        Finset.single_le_sum (fun i _ => mul_nonneg (abs_nonneg _) (hKj_pos i).le) hj_mem
      calc ‖iteratedFDeriv ℝ j (fun y : ℝ × Plane => tr.p y.1 y.2) (x.2.2, (x.1, x.2.1))‖
          ≤ C_j j * Real.exp (-(κ_j j * x.2.2)) := hbd_j j (x.2.2, (x.1, x.2.1)) hx0
        _ ≤ |C_j j| * Real.exp (-(κ_j j * x.2.2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)
        _ ≤ |C_j j| * (K_j j * x.2.2 ^ (-(K : ℝ))) :=
            mul_le_mul_of_nonneg_left (hExp_j j x.2.2 hx1) (abs_nonneg _)
        _ = (|C_j j| * K_j j) * x.2.2 ^ (-(K : ℝ)) := by ring
        _ ≤ C_u * x.2.2 ^ (-(K : ℝ)) :=
            mul_le_mul_of_nonneg_right hj_le (Real.rpow_nonneg hx0.le _)
  -- 3. `RapidProf (Jet.A2.stressFam ν c tr)`
  have hRapid_stress : RapidProf (Jet.A2.stressFam ν c tr) := by
    intro m w K
    have hsm1D := PartI.PartI_T23.contDiffOn_meanStress hc0 tr
    obtain ⟨hsm, hnorm⟩ := pullback_1d_smooth_and_jet hsm1D
    set W : ℕ := 2 ^ m * w
    obtain ⟨C_w, κ_w, hCw_pos, hκw_pos, hbd_w⟩ := hStressW ν hν hν_sw_le tr htr W
    obtain ⟨K_w, hKw_pos, hExp_w⟩ := exp_neg_le_rpow_any κ_w hκw_pos (-(K : ℝ))
    have hStressMix :=
      meanStress_unweighted_jet_of_velFluct hν hc0 tr htr (hVPFix ν hν hν_vp_le tr htr).1
    have hStressJoint : ∀ j : ℕ, ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        ‖iteratedFDeriv ℝ j (Jet.A2.stressFam ν c tr) x‖ ≤ Cj * x.2.2 ^ (-(K : ℝ)) := by
      intro j
      obtain ⟨Kj, hKj0, hJ⟩ := PartI.jointFromMixed1D j
      choose C_ℓ κ_ℓ hC_ℓ hκ_ℓ hbd_ℓ using fun ℓ : ℕ => hStressMix (j - ℓ) ℓ
      choose K_ℓ hKℓ_pos hExp_ℓ using fun ℓ : ℕ =>
        exp_neg_le_rpow_any (κ_ℓ ℓ) (hκ_ℓ ℓ) (-(K : ℝ))
      set B_j : ℝ := Kj * ∑ ℓ ∈ Finset.range (j + 1), C_ℓ ℓ * K_ℓ ℓ
      refine ⟨B_j, mul_nonneg hKj0
        (Finset.sum_nonneg fun ℓ _ => mul_nonneg (hC_ℓ ℓ).le (hKℓ_pos ℓ).le),
        fun x hx1 => ?_⟩
      have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      have h1 := (hnorm x hx0 j).trans (hJ (PartI.meanStress tr) hsm1D (x.2.2, x.2.1) hx0)
      have hsum : ∑ ℓ ∈ Finset.range (j + 1),
          ‖iteratedDeriv (j - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => PartI.meanStress tr r e) x.2.2) x.2.1‖ ≤
          (∑ ℓ ∈ Finset.range (j + 1), C_ℓ ℓ * K_ℓ ℓ) * x.2.2 ^ (-(K : ℝ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun ℓ _ => ?_
        rw [Real.norm_eq_abs]
        calc |iteratedDeriv (j - ℓ)
                (fun e => iteratedDeriv ℓ (fun r => PartI.meanStress tr r e) x.2.2) x.2.1|
            ≤ C_ℓ ℓ * Real.exp (-(κ_ℓ ℓ * x.2.2)) := hbd_ℓ ℓ x.2.2 hx0 x.2.1
          _ ≤ C_ℓ ℓ * (K_ℓ ℓ * x.2.2 ^ (-(K : ℝ))) :=
              mul_le_mul_of_nonneg_left (hExp_ℓ ℓ x.2.2 hx1) (hC_ℓ ℓ).le
          _ = C_ℓ ℓ * K_ℓ ℓ * x.2.2 ^ (-(K : ℝ)) := by ring
      calc ‖iteratedFDeriv ℝ j (Jet.A2.stressFam ν c tr) x‖
          ≤ Kj * ∑ ℓ ∈ Finset.range (j + 1),
              ‖iteratedDeriv (j - ℓ)
                (fun e => iteratedDeriv ℓ (fun r => PartI.meanStress tr r e) x.2.2) x.2.1‖ := h1
        _ ≤ Kj * ((∑ ℓ ∈ Finset.range (j + 1), C_ℓ ℓ * K_ℓ ℓ) * x.2.2 ^ (-(K : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum hKj0
        _ = B_j * x.2.2 ^ (-(K : ℝ)) := by unfold B_j; ring
    choose C_j hCj0 hbd_j using hStressJoint
    set C₀ : ℝ := 2 ^ W * C_w * K_w
    have hC₀0 : 0 ≤ C₀ := by unfold C₀; positivity
    set C_u : ℝ := ∑ j ∈ Finset.range (m + 2), C_j j
    refine wtdProfJet_of_zero_and_unweighted (C₀ := C₀) (C_u := C_u) hsm hC₀0
      (Finset.sum_nonneg fun j _ => hCj0 j)
      (fun x hx1 => ?_) (fun x hx1 j hj => ?_)
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      have h_eta : 1 + |x.2.1| ≤ 2 * (1 + x.2.1 ^ 2) := by
        nlinarith [sq_nonneg (|x.2.1| - 1), sq_abs x.2.1, abs_nonneg x.2.1]
      have h_pow : (1 + |x.2.1|) ^ W ≤ 2 ^ W * (1 + x.2.1 ^ 2) ^ W := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h_eta W
      calc (1 + |x.2.1|) ^ W * |Jet.A2.stressFam ν c tr x|
          ≤ (2 ^ W * (1 + x.2.1 ^ 2) ^ W) * |PartI.meanStress tr x.2.2 x.2.1| :=
            mul_le_mul_of_nonneg_right h_pow (abs_nonneg _)
        _ = 2 ^ W * ((1 + x.2.1 ^ 2) ^ W * |PartI.meanStress tr x.2.2 x.2.1|) := by ring
        _ ≤ 2 ^ W * (C_w * Real.exp (-(κ_w * x.2.2))) :=
            mul_le_mul_of_nonneg_left (hbd_w x.2.2 hx0 x.2.1) (by positivity)
        _ ≤ 2 ^ W * (C_w * (K_w * x.2.2 ^ (-(K : ℝ)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hExp_w x.2.2 hx1) hCw_pos.le) (by positivity)
        _ = C₀ * x.2.2 ^ (-(K : ℝ)) := by unfold C₀; ring
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      have hj_le : C_j j ≤ C_u :=
        Finset.single_le_sum (fun i _ => hCj0 i) (Finset.mem_range.2 (by omega))
      exact (hbd_j j x hx1).trans
        (mul_le_mul_of_nonneg_right hj_le (Real.rpow_nonneg hx0.le _))
  -- 4. `EvRapidProf (fun M => remFam M ν c tr)`
  have hEvRapid_rem : EvRapidProf (fun M => remFam M ν c tr) := by
    intro m w K
    set W : ℕ := 2 ^ m * w
    refine ⟨W + K, fun M hM => ?_⟩
    have hsm1D :=
      meanRemainderSmooth_of PartI.trainMeanEquations_proof heatKernelIterSmooth ν c hν hc0 tr htr M
    obtain ⟨hsm, hnorm⟩ := pullback_1d_smooth_and_jet hsm1D
    obtain ⟨B_tail, hBt0, hR2⟩ := hRegime2 W K
    obtain ⟨B_hs, hBhs0, hHs⟩ := heatSumFam_far_eta_bound hν hν1 c tr M W K
    choose C_j hbd_j using fun j : ℕ => hRemFix ν hν hν_rm_le tr htr M j
    set C₀ : ℝ := max (A_reg ^ W * |C_j 0|) (B_tail + B_hs)
    set C_u : ℝ := ∑ j ∈ Finset.range (m + 2), |C_j j|
    refine wtdProfJet_of_zero_and_unweighted (C₀ := C₀) (C_u := C_u) hsm
      (le_max_of_le_right (add_nonneg hBt0 hBhs0))
      (Finset.sum_nonneg fun j _ => abs_nonneg _)
      (fun x hx1 => ?_) (fun x hx1 j hj => ?_)
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      rcases le_or_gt |x.2.1| (C'_T / ν + 2 + x.2.2) with hη | hη
      · have hw_le := hRegime1_wpow W x.2.2 x.2.1 hx1 hη
        have hu0 := hbd_j 0 (x.2.2, x.2.1) hx1
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hu0
        have hu0' : |remFam M ν c tr x| ≤ |C_j 0| * x.2.2 ^ (-(M : ℝ) - 3 / 2) :=
          hu0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx0.le _))
        have hexp_le : (W : ℝ) + (-(M : ℝ) - 3 / 2) ≤ -(K : ℝ) := by
          have hM_real : (W : ℝ) + (K : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
          linarith
        have hs_le : x.2.2 ^ (W : ℝ) * x.2.2 ^ (-(M : ℝ) - 3 / 2) ≤ x.2.2 ^ (-(K : ℝ)) := by
          rw [← Real.rpow_add hx0]
          exact Real.rpow_le_rpow_of_exponent_le hx1 hexp_le
        calc (1 + |x.2.1|) ^ W * |remFam M ν c tr x|
            ≤ (A_reg ^ W * x.2.2 ^ (W : ℝ)) * (|C_j 0| * x.2.2 ^ (-(M : ℝ) - 3 / 2)) :=
              mul_le_mul hw_le hu0' (abs_nonneg _) (by positivity)
          _ = (A_reg ^ W * |C_j 0|) * (x.2.2 ^ (W : ℝ) * x.2.2 ^ (-(M : ℝ) - 3 / 2)) := by ring
          _ ≤ (A_reg ^ W * |C_j 0|) * x.2.2 ^ (-(K : ℝ)) :=
              mul_le_mul_of_nonneg_left hs_le (by positivity)
          _ ≤ C₀ * x.2.2 ^ (-(K : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
      · have hs_le_eta : x.2.2 ≤ |x.2.1| := by
          have : 0 < C'_T / ν + 2 := by positivity
          linarith
        have h_mean := (hR2 x.2.2 x.2.1 hx1 hη.le).2.2
        have h_hs := hHs x hx1 hs_le_eta
        have h_decomp : remFam M ν c tr x =
            PartI.meanStream tr x.2.2 x.2.1 - heatSumFam M ν c tr x := by
          have h := congr_fun (congr_fun (congr_fun
            (congr_fun (meanFam_eq_heatSum_add_rem M) ν) c) tr) x
          change PartI.meanStream tr x.2.2 x.2.1 =
            heatSumFam M ν c tr x + remFam M ν c tr x at h
          linarith
        dsimp only
        rw [h_decomp]
        calc (1 + |x.2.1|) ^ W * |PartI.meanStream tr x.2.2 x.2.1 - heatSumFam M ν c tr x|
            ≤ (1 + |x.2.1|) ^ W * |PartI.meanStream tr x.2.2 x.2.1| +
                (1 + |x.2.1|) ^ W * |heatSumFam M ν c tr x| := by
              rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
          _ ≤ B_tail * x.2.2 ^ (-(K : ℝ)) + B_hs * x.2.2 ^ (-(K : ℝ)) :=
              add_le_add h_mean h_hs
          _ = (B_tail + B_hs) * x.2.2 ^ (-(K : ℝ)) := by ring
          _ ≤ C₀ * x.2.2 ^ (-(K : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
    · have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
      have hj_le : |C_j j| ≤ C_u :=
        Finset.single_le_sum (f := fun i => |C_j i|)
          (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
      have hexp_le : -(M : ℝ) - 3 / 2 ≤ -(K : ℝ) := by
        have hKM : (K : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.le_add_left K W).trans hM
        linarith
      dsimp only
      calc ‖iteratedFDeriv ℝ j (remFam M ν c tr) x‖
          ≤ ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => PartI.meanRemainder tr M y.1 y.2)
              (x.2.2, x.2.1)‖ := hnorm x hx0 j
        _ ≤ C_j j * x.2.2 ^ (-(M : ℝ) - 3 / 2) := hbd_j j (x.2.2, x.2.1) hx1
        _ ≤ |C_j j| * x.2.2 ^ (-(M : ℝ) - 3 / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx0.le _)
        _ ≤ |C_j j| * x.2.2 ^ (-(K : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hexp_le) (abs_nonneg _)
        _ ≤ C_u * x.2.2 ^ (-(K : ℝ)) :=
            mul_le_mul_of_nonneg_right hj_le (Real.rpow_nonneg hx0.le _)
  exact ⟨hRapid_fluct, hRapid_pres, hRapid_stress, hEvRapid_rem⟩

/-! ### 4. All nine residual/remainder blocks from the base-family bounds -/

/-- If `f` agrees on `ageDomain` with `g₁ + g₂` where `g₁, g₂` are `C^∞` on `ageDomain` and
`QConst g₁`, then `partialQ f` agrees on `ageDomain` with `partialQ g₂`. -/
theorem eqOn_partialQ_of_qConst_add {f g₁ g₂ : ProfilePoint → ℝ}
    (hg₁ : ContDiffOn ℝ ∞ g₁ ageDomain) (hg₂ : ContDiffOn ℝ ∞ g₂ ageDomain)
    (hq₁ : QConst g₁) (hfg : EqOn (fun y => g₁ y + g₂ y) f ageDomain) :
    EqOn (UnforcedLeray.B0184.partialQ g₂) (UnforcedLeray.B0184.partialQ f) ageDomain := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] (g₁ + g₂) :=
    Filter.eventuallyEq_of_mem (B0185.isOpen_ageDomain.mem_nhds hx) fun y hy => (hfg hy).symm
  have hd₁ : DifferentiableAt ℝ g₁ x :=
    (hg₁.contDiffAt (B0185.isOpen_ageDomain.mem_nhds hx)).differentiableAt (by simp)
  have hd₂ : DifferentiableAt ℝ g₂ x :=
    (hg₂.contDiffAt (B0185.isOpen_ageDomain.mem_nhds hx)).differentiableAt (by simp)
  unfold UnforcedLeray.B0184.partialQ
  rw [hev.fderiv_eq, (hd₁.hasFDerivAt.add hd₂.hasFDerivAt).fderiv]
  change partialQ g₂ x = partialQ g₁ x + partialQ g₂ x
  rw [hq₁.partialQ_eq_zero x, zero_add]

/-- Derives `RapidProf` for all five `M`-independent fluctuation/pressure/`A₂` blocks and
`EvRapidProf` for all four mean remainder blocks from the base-family bounds. -/
theorem all_nine_blocks_from_base {ν c : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hc0 : 0 < c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hFl : RapidProf (Jet.fluctFam ν c tr))
    (hPr : RapidProf (Jet.presFam ν c tr))
    (hSt : RapidProf (Jet.A2.stressFam ν c tr))
    (hRm : EvRapidProf (fun M => remFam M ν c tr)) :
    RapidProf (fluctA1 ν c tr) ∧
    RapidProf (fluctB1 ν c tr) ∧
    RapidProf (coefA2Fam ν c tr) ∧
    RapidProf (Jet.B2.fluctB2 ν c tr) ∧
    RapidProf (fluctB3 ν c tr) ∧
    EvRapidProf (fun M => remB1 M ν c tr) ∧
    EvRapidProf (fun M => remB3 M ν c tr) ∧
    EvRapidProf (fun M => remA1 M ν c tr) ∧
    EvRapidProf (fun M => BlockB2Sub.remB2 M ν c tr) := by
  have hT := Jet.jetToolkit
  have hFW := fluctWords_uncond
  have hMW := meanWords_uncond
  -- `UnifTempProf` for `heatSumFam` and `TempProf` for `meanFam`, `psiFam`:
  have hHS_ut : UnifTempProf (fun M => heatSumFam M ν c tr) := by
    intro m w
    refine ⟨w + m, fun M => ?_⟩
    have h := heatSumFam_wtdProfJet hν0 hν1 c tr M m w
    have hexp : (w : ℝ) + (m : ℝ) = ((w + m : ℕ) : ℝ) := by push_cast; ring
    rwa [hexp] at h
  have hMean_t : TempProf (Jet.meanFam ν c tr) := by
    intro m w
    obtain ⟨M₀, hM₀⟩ := hRm m w 0
    have h1 := heatSumFam_wtdProfJet hν0 hν1 c tr M₀ m w
    have h2 := (hM₀ M₀ le_rfl).mono_alpha
      (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) w, Nat.cast_nonneg (α := ℝ) m] :
        -((0 : ℕ) : ℝ) ≤ (w : ℝ) + (m : ℝ))
    have hsum := h1.add h2
    have hexp : (w : ℝ) + (m : ℝ) = ((w + m : ℕ) : ℝ) := by push_cast; ring
    rw [hexp] at hsum
    refine ⟨w + m, hsum.congr fun x _ => ?_⟩
    have h := congr_fun (congr_fun (congr_fun
      (congr_fun (meanFam_eq_heatSum_add_rem M₀) ν) c) tr) x
    exact h.symm
  have hPsi_t : TempProf (Jet.psiFam ν c tr) := by
    refine (hMean_t.add hFl.toTemp).congr fun x _ => ?_
    rw [Jet.psiFam_eq]; rfl
  -- Derived `RapidProf` and `TempProf` velocity/defect families:
  have hv1bar_t : TempProf (Jet.B2.v1bar ν c tr) := hMean_t.partialEta.neg
  have hhbar_t : TempProf (Jet.B2.hbar ν c tr) := hMean_t.sub hMean_t.ageOp
  have hv1P_t : TempProf (Jet.B2.v1P ν c tr) := hPsi_t.partialEta.neg
  have hhP_t : TempProf (Jet.B2.hP ν c tr) := hPsi_t.sub hPsi_t.ageOp
  have hv1t_r : RapidProf (Jet.B2.v1t ν c tr) := hFl.partialEta.neg
  have hht_r : RapidProf (Jet.B2.ht ν c tr) := hFl.sub hFl.ageOp
  have hv2P_r : RapidProf (Jet.B2.v2P ν c tr) := by
    have hsm_m := (hMean_t 0 0).choose_spec.1
    have hsm_f := (hFl 0 0 0).1
    refine hFl.partialQ.congr (eqOn_partialQ_of_qConst_add hsm_m hsm_f
      (QConstFam.meanFam ν c tr) fun x _ => ?_)
    change Jet.meanFam ν c tr x + Jet.fluctFam ν c tr x = Jet.psiFam ν c tr x
    rw [Jet.psiFam_eq]; rfl
  have hqv1P_r : RapidProf (Jet.famQ Jet.B2.v1P ν c tr) := by
    have hsm1 := (hv1bar_t 0 0).choose_spec.1
    have hsm2 := (hv1t_r 0 0 0).1
    exact hv1t_r.partialQ.congr (eqOn_partialQ_of_qConst_add hsm1 hsm2
      (QConstFam.v1bar ν c tr) fun x hx =>
        (Jet.B2.v1P_split hT hFW hMW ν c hν0 hc0 tr htr hx).symm)
  have hqhP_eq : EqOn (UnforcedLeray.B0184.partialQ (Jet.B2.ht ν c tr))
      (Jet.famQ Jet.B2.hP ν c tr) ageDomain := by
    have hsm1 := (hhbar_t 0 0).choose_spec.1
    have hsm2 := (hht_r 0 0 0).1
    exact eqOn_partialQ_of_qConst_add hsm1 hsm2 (QConstFam.hbar ν c tr) fun x hx =>
      (Jet.B2.hP_split hT hFW hMW ν c hν0 hc0 tr htr hx).symm
  have hqhP_r : RapidProf (Jet.famQ Jet.B2.hP ν c tr) :=
    hht_r.partialQ.congr hqhP_eq
  have hqqhP_r : RapidProf (Jet.famQ (Jet.famQ Jet.B2.hP) ν c tr) :=
    hht_r.partialQ.partialQ.congr (eqOn_dirDeriv_ageDomain eqDir hqhP_eq)
  -- 1. `fluctB1`:
  have h_fluctB1 : RapidProf (fluctB1 ν c tr) :=
    (((hv1t_r.ageShift 2).ageOp).const_mul ν).neg.congr fun x hx =>
      (fluctB1_late hT hFW hMW ν c hν0 hc0 tr htr hx).symm
  -- 2. `fluctB3`:
  have h_fluctB3 : RapidProf (fluctB3 ν c tr) :=
    ((((hht_r.ageShift 1).ageShift 1)).const_mul ν).neg.congr fun x hx =>
      (fluctB3_late hT hFW hMW ν c hν0 hc0 tr htr hx).symm
  -- 3. `fluctA1`:
  have h_fluctA1 : RapidProf (fluctA1 ν c tr) := by
    have t1 := (hv1t_r.mul_temp hv1P_t.ageOp).neg
    have t2 := hv1bar_t.mul_rapid hv1t_r.ageOp
    have t3 := hht_r.mul_temp hv1P_t.partialEta
    have t4 := hhbar_t.mul_rapid hv1t_r.partialEta
    have t5 := hv1t_r.mul_temp hv1P_t
    have t6 := hv1bar_t.mul_rapid hv1t_r
    have t7 := ((hqv1P_r.ageShift 1).const_mul ν).const_mul 2
    have t8 := hPr.ageShift 2
    have hsum := ((((((t1.sub t2).add t3).add t4).sub t5).sub t6).add t7).sub t8
    exact hsum.congr fun x hx => (fluctA1_late hT hFW hMW ν c hν0 hc0 tr htr hx).symm
  -- 4. `Jet.B2.fluctB2`:
  have h_fluctB2 : RapidProf (Jet.B2.fluctB2 ν c tr) := by
    have t1 := (hv1t_r.mul_temp (hhP_t.ageShift 1)).neg
    have t2 := hv1bar_t.mul_rapid (hht_r.ageShift 1)
    have t3 := hht_r.mul_temp hhP_t.partialEta
    have t4 := hhbar_t.mul_rapid hht_r.partialEta
    have t5 := ((hqhP_r.ageShift 1).const_mul ν).const_mul 2
    have t6 := ((hv2P_r.ageShift 1).ageShift 1).const_mul ν
    have hsum := ((((t1.sub t2).add t3).add t4).add t5).sub t6
    exact hsum.congr fun x hx => (Jet.B2.fluct_eq hT hFW hMW ν c hν0 hc0 tr htr hx).symm
  -- 5. `coefA2Fam`:
  have h_coefA2 : RapidProf (coefA2Fam ν c tr) := by
    have hcancel := Jet.A2.meanStressCancel_of hT Jet.A2.heatOpLin
      (Jet.A2.heatOpK_of lateIngredients.comm hT.comm)
      (Jet.A2.meanHeatEq_of PartI.trainMeanEquations_proof) hMW.1
    have hsplit := Jet.A2.heat_defect_split hT Jet.A2.ageSmoothLocal Jet.A2.heatOpLin
      hMW.1 hFW.1.1
    have hheat_mean : RapidProf (Jet.A2.heatOp Jet.A2.defectMean ν c tr) :=
      (hSt.ageShift 1).neg.congr fun x hx => (hcancel ν c hν0 hc0 tr htr hx).symm
    have hheat_fluct : RapidProf (Jet.A2.heatOp Jet.A2.defectFluct ν c tr) :=
      hht_r.partialAge.sub (hht_r.partialEta.partialEta.const_mul ν)
    have hheat_def : RapidProf (Jet.A2.heatOp Jet.A2.defectFam ν c tr) :=
      (hheat_mean.add hheat_fluct).congr fun x hx => (hsplit ν c hν0 hc0 tr htr hx).symm
    -- Notice `Jet.A2.v1 = Jet.B2.v1P`, `Jet.A2.v2 = Jet.B2.v2P`, `Jet.A2.defectFam = Jet.B2.hP`:
    have a1 := hv1P_t.mul_rapid hqhP_r
    have a2 := hv2P_r.mul_temp hhP_t.partialEta
    have a3 := hqqhP_r.const_mul ν
    have a4 := hhP_t.mul_rapid hv2P_r.partialEta
    have a5 := hv1P_t.mul_rapid (hv2P_r.ageShift 1)
    have a6 := ((hv2P_r.partialQ.ageShift 1).const_mul ν).const_mul 2
    have hsum := (((((hheat_def.add a1).add a2).sub a3).add a4).sub a5).add a6
    exact hsum.congr fun x hx => Jet.A2.coeffA2_late ν c hν0 hc0 tr htr hx
  -- 6. `remB1`:
  have h_remB1 : EvRapidProf (fun M => remB1 M ν c tr) :=
    ((((hRm.partialEta.neg.ageShift 2).ageOp).const_mul ν).neg).congr fun M x hx =>
      (remB1_late M ν c hν0 hc0 tr htr hx).symm
  -- 7. `remB3`:
  have h_remB3 : EvRapidProf (fun M => remB3 M ν c tr) :=
    (((((hRm.sub hRm.ageOp).ageShift 1).ageShift 1).const_mul ν).neg).congr fun M x hx =>
      (remB3_late M ν c hν0 hc0 tr htr hx).symm
  -- 8. `remA1`:
  have h_remA1 : EvRapidProf (fun M => remA1 M ν c tr) := by
    have hv1H_ut : UnifTempProf (fun M => v1H M ν c tr) := hHS_ut.partialEta.neg
    have hhH_ut : UnifTempProf (fun M => hH M ν c tr) := hHS_ut.sub hHS_ut.ageOp
    have hv1R_ev : EvRapidProf (fun M => v1R M ν c tr) := hRm.partialEta.neg
    have hhR_ev : EvRapidProf (fun M => hR M ν c tr) := hRm.sub hRm.ageOp
    have p1 := hhH_ut.mul_evRapid hv1R_ev.partialEta
    have p2 := hhR_ev.mul_unifTemp hv1H_ut.partialEta
    have p3 := hhR_ev.mul_evRapid hv1R_ev.partialEta
    have q1 := hv1H_ut.mul_evRapid (hv1R_ev.ageShift 1)
    have q2 := hv1R_ev.mul_unifTemp (hv1H_ut.ageShift 1)
    have q3 := hv1R_ev.mul_evRapid (hv1R_ev.ageShift 1)
    exact (((p1.add p2).add p3).sub ((q1.add q2).add q3)).congr fun M x hx =>
      (remA1_late M ν c hν0 hc0 tr htr hx).symm
  -- 9. `BlockB2Sub.remB2` (note `BlockB2Sub.S_heat = heatSumFam` and `BlockB2Sub.remFamN = remFam` by `rfl`):
  have h_remB2 : EvRapidProf (fun M => BlockB2Sub.remB2 M ν c tr) := by
    have hMean_ut : UnifTempProf (fun _ => Jet.meanFam ν c tr) := hMean_t.toUnif
    have hv1_S : UnifTempProf (fun M => BlockB2Sub.v1Op (BlockB2Sub.S_heat M) ν c tr) :=
      hHS_ut.partialEta.neg
    have hh_S : UnifTempProf (fun M => BlockB2Sub.hOp (BlockB2Sub.S_heat M) ν c tr) :=
      hHS_ut.sub hHS_ut.ageOp
    have hv1_R : EvRapidProf (fun M => BlockB2Sub.v1Op (BlockB2Sub.remFamN M) ν c tr) :=
      hRm.partialEta.neg
    have hh_R : EvRapidProf (fun M => BlockB2Sub.hOp (BlockB2Sub.remFamN M) ν c tr) :=
      hRm.sub hRm.ageOp
    have hh_M : UnifTempProf (fun _ => BlockB2Sub.hOp Jet.meanFam ν c tr) :=
      hMean_ut.sub hMean_ut.ageOp
    have b1 := (hv1_S.mul_evRapid (hh_R.ageShift 1)).neg.add (hh_S.mul_evRapid hh_R.partialEta)
    have b2 := (hv1_R.mul_unifTemp (hh_M.ageShift 1)).neg.add (hh_R.mul_unifTemp hh_M.partialEta)
    exact b1.add b2
  exact ⟨h_fluctA1, h_fluctB1, h_coefA2, h_fluctB2, h_fluctB3,
    h_remB1, h_remB3, h_remA1, h_remB2⟩

/-! ### 5. Total meridional remainder `r_rem_total p M`, lift identity, and `chartSwap` jet bound -/

/-- Radial scalar remainder profile on `ProfilePoint` at expansion order `M`. -/
def f_rem_rad (p : Params) (M : ℕ) (x : ProfilePoint) : ℝ :=
  ringEps p.R ^ 2 * remB1 M p.ν p.c p.train x +
    ringEps p.R * remA1 M p.ν p.c p.train x +
    ringEps p.R * fluctA1 p.ν p.c p.train x +
    ringEps p.R ^ 2 * fluctB1 p.ν p.c p.train x

/-- Axial scalar remainder profile on `ProfilePoint` at expansion order `M`. -/
def f_rem_ax (p : Params) (M : ℕ) (x : ProfilePoint) : ℝ :=
  ringEps p.R ^ 3 * remB3 M p.ν p.c p.train x +
    ringEps p.R ^ 2 * BlockB2Sub.remB2 M p.ν p.c p.train x +
    ringEps p.R * coefA2Fam p.ν p.c p.train x +
    ringEps p.R ^ 2 * Jet.B2.fluctB2 p.ν p.c p.train x +
    ringEps p.R ^ 3 * fluctB3 p.ν p.c p.train x

/-- Total meridional remainder chart profile on `{w | 0 < w.1}` at expansion order `M`. -/
def r_rem_total (p : Params) (M : ℕ) (w : ℝ × (ℝ × ℝ)) : Axi.Merid :=
  f_rem_rad p M (chartSwap w) • meridE0 + f_rem_ax p M (chartSwap w) • meridE1

/-- Off-axis identity splitting `Axi.age p.R z • Axi.Nv p.R (resChartProfile p) τ z` into the
Cartesian heat sum `F_heat_total p M z` and the lifted remainder `r_rem_total p M`. -/
theorem late_lift_decomp_off_axis (p : Params) (htr : IsBUCTrain p.train) (hR : 2 ≤ p.R)
    (M : ℕ) (τ : ℝ) {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age p.R z • Axi.Nv p.R (resChartProfile p) τ z =
      F_heat_total p M z + Axi.age p.R z • Axi.Nv p.R (r_rem_total p M) τ z := by
  have hR0 : 0 < p.R := by linarith
  have hchart_pos : 0 < (Axi.chart p.R τ z).1 := by
    show 0 < Axi.age p.R z
    unfold Axi.age
    exact div_pos (pow_pos hR0 2) (pow_pos (Axi.ϱ_pos hz) 2)
  have hpt := resChartProfile_eq_blocks_add_fluct p htr hchart_pos
  have hr_eq : r_rem_total p M (Axi.chart p.R τ z) =
      (ringEps p.R ^ 2 * remB1 M p.ν p.c p.train (chartSwap (Axi.chart p.R τ z))) • meridE0 +
      (ringEps p.R ^ 3 * remB3 M p.ν p.c p.train (chartSwap (Axi.chart p.R τ z))) • meridE1 +
      (ringEps p.R * remA1 M p.ν p.c p.train (chartSwap (Axi.chart p.R τ z))) • meridE0 +
      (ringEps p.R ^ 2 * BlockB2Sub.remB2 M p.ν p.c p.train (chartSwap (Axi.chart p.R τ z))) •
        meridE1 +
      fluctPolyMerid p (chartSwap (Axi.chart p.R τ z)) := by
    ext i
    fin_cases i <;>
      simp [r_rem_total, f_rem_rad, f_rem_ax, fluctPolyMerid, meridE0, meridE1] <;> ring
  have hNv_eq :
      Axi.Nv p.R (resChartProfile p) τ z =
        Axi.Nv p.R (fun w =>
          (ringEps p.R ^ 2 * meanB1 p.ν p.c p.train (chartSwap w)) • meridE0) τ z +
        Axi.Nv p.R (fun w =>
          (ringEps p.R ^ 3 * meanB3 p.ν p.c p.train (chartSwap w)) • meridE1) τ z +
        Axi.Nv p.R (fun w =>
          (ringEps p.R * meanA1 p.ν p.c p.train (chartSwap w)) • meridE0) τ z +
        Axi.Nv p.R (fun w =>
          (ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train (chartSwap w)) • meridE1) τ z +
        Axi.Nv p.R (fun w => fluctPolyMerid p (chartSwap w)) τ z := by
    simp only [Axi.Nv, hpt, map_add, smul_add]
  have hNv_rem :
      Axi.Nv p.R (r_rem_total p M) τ z =
        Axi.Nv p.R (fun w =>
          (ringEps p.R ^ 2 * remB1 M p.ν p.c p.train (chartSwap w)) • meridE0) τ z +
        Axi.Nv p.R (fun w =>
          (ringEps p.R ^ 3 * remB3 M p.ν p.c p.train (chartSwap w)) • meridE1) τ z +
        Axi.Nv p.R (fun w =>
          (ringEps p.R * remA1 M p.ν p.c p.train (chartSwap w)) • meridE0) τ z +
        Axi.Nv p.R (fun w =>
          (ringEps p.R ^ 2 * BlockB2Sub.remB2 M p.ν p.c p.train (chartSwap w)) • meridE1) τ z +
        Axi.Nv p.R (fun w => fluctPolyMerid p (chartSwap w)) τ z := by
    simp only [Axi.Nv, hr_eq, map_add, smul_add]
  have hd1 := heatB1_lift_decomp p M τ hz
  have hd2 := heatB3_lift_decomp p M τ hz
  have hd3 := heatA1_lift_decomp p M τ hz
  have hd4 := BlockB2Sub.meanB2_lift_decomp p htr hR M τ hz
  rw [hNv_eq, hNv_rem]
  simp only [F_heat_total, smul_add]
  rw [hd1, hd2, hd3, hd4]
  abel

/-- Converts `WtdProfJet m w α` on `f₀, f₁ : ProfilePoint → ℝ` into a weighted `iteratedFDeriv`
bound on `w' ↦ f₀ (chartSwap w') • meridE0 + f₁ (chartSwap w') • meridE1`. -/
theorem merid_chartSwap_jet_of_wtdProfJet {m w : ℕ} {α : ℝ} {f₀ f₁ : ProfilePoint → ℝ}
    (h₀ : WtdProfJet m w α f₀) (h₁ : WtdProfJet m w α f₁) :
    ContDiffOn ℝ ∞ (fun w' => f₀ (chartSwap w') • meridE0 + f₁ (chartSwap w') • meridE1)
      {w' : ℝ × (ℝ × ℝ) | 0 < w'.1} ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w' : ℝ × (ℝ × ℝ), 1 ≤ w'.1 → ∀ l ≤ m,
      (1 + |w'.2.2|) ^ w *
        ‖iteratedFDeriv ℝ l
          (fun u => f₀ (chartSwap u) • meridE0 + f₁ (chartSwap u) • meridE1) w'‖ ≤
        B * w'.1 ^ α := by
  obtain ⟨c₀, C₀, hC₀0, hb₀⟩ := h₀
  obtain ⟨c₁, C₁, hC₁0, hb₁⟩ := h₁
  let F : ProfilePoint → Axi.Merid := fun x => f₀ x • meridE0 + f₁ x • meridE1
  have cF : ContDiffOn ℝ ∞ F ageDomain :=
    (c₀.smul contDiffOn_const).add (c₁.smul contDiffOn_const)
  refine ⟨cF.comp chartSwapLIE.contDiff.contDiffOn fun w' hw' => hw',
    C₀ + C₁, add_nonneg hC₀0 hC₁0, fun w' hw'1 l hl => ?_⟩
  rw [norm_iteratedFDeriv_comp_chartSwap F w' l]
  set x : ProfilePoint := chartSwap w'
  have hx1 : 1 ≤ x.2.2 := hw'1
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hnhds : ageDomain ∈ 𝓝 x := B0185.isOpen_ageDomain.mem_nhds hx0
  have cf₀ : ContDiffAt ℝ ∞ f₀ x := c₀.contDiffAt hnhds
  have cf₁ : ContDiffAt ℝ ∞ f₁ x := c₁.contDiffAt hnhds
  have hadd : iteratedFDeriv ℝ l F x =
      iteratedFDeriv ℝ l (fun y => f₀ y • meridE0) x +
        iteratedFDeriv ℝ l (fun y => f₁ y • meridE1) x :=
    iteratedFDeriv_add_apply ((cf₀.smul contDiffAt_const).of_le (by exact_mod_cast le_top))
      ((cf₁.smul contDiffAt_const).of_le (by exact_mod_cast le_top))
  have hnorm : ‖iteratedFDeriv ℝ l F x‖ ≤
      ‖iteratedFDeriv ℝ l f₀ x‖ + ‖iteratedFDeriv ℝ l f₁ x‖ := by
    rw [hadd]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_iteratedFDeriv_smul_merid_le cf₀ meridE0 norm_merid_e0.le l)
        (norm_iteratedFDeriv_smul_merid_le cf₁ meridE1 norm_merid_e1.le l))
  have hw0 : 0 ≤ (1 + |w'.2.2|) ^ w := by positivity
  calc (1 + |w'.2.2|) ^ w * ‖iteratedFDeriv ℝ l F x‖
      ≤ (1 + |w'.2.2|) ^ w * (‖iteratedFDeriv ℝ l f₀ x‖ + ‖iteratedFDeriv ℝ l f₁ x‖) :=
        mul_le_mul_of_nonneg_left hnorm hw0
    _ = (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l f₀ x‖ +
          (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l f₁ x‖ := by
        change (1 + |w'.2.2|) ^ w * _ = (1 + |w'.2.2|) ^ w * _ + (1 + |w'.2.2|) ^ w * _
        ring
    _ ≤ C₀ * x.2.2 ^ α + C₁ * x.2.2 ^ α := add_le_add (hb₀ x hx1 l hl) (hb₁ x hx1 l hl)
    _ = (C₀ + C₁) * w'.1 ^ α := by change _ = (C₀ + C₁) * x.2.2 ^ α; ring

/-- **Main remainder-jet theorem at a single viscosity threshold `ν₀ > 0`**:
for all `p : Params` with `IsBUCTrain p.train`, `p.ν < ν₀`, `p.c = (p.ν ^ 2)⁻¹`, and every
`(m, w, K : ℕ)`, there exists an expansion order `M : ℕ` such that `r_rem_total p M` is `C^∞` on
`{w' | 0 < w'.1}` and satisfies `(1 + |w'.2.2|)^w ‖D^l(r_rem_total p M)(w')‖ ≤ B (w'.1)^{-K}`
on `1 ≤ w'.1` for all `l ≤ m`. -/
theorem exists_late_rem_total_jet :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ → p.c = (p.ν ^ 2)⁻¹ →
        ∀ m w K : ℕ, ∃ M : ℕ,
          ContDiffOn ℝ ∞ (r_rem_total p M) {w' : ℝ × (ℝ × ℝ) | 0 < w'.1} ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ w' : ℝ × (ℝ × ℝ), 1 ≤ w'.1 → ∀ l ≤ m,
            (1 + |w'.2.2|) ^ w * ‖iteratedFDeriv ℝ l (r_rem_total p M) w'‖ ≤
              B * w'.1 ^ (-(K : ℝ)) := by
  obtain ⟨ν₀, hν₀, hν₀_le1, HBase⟩ := exists_base_family_jets
  refine ⟨ν₀, hν₀, fun p htr hν hc m w K => ?_⟩
  have hν1 : p.ν ≤ 1 := hν.le.trans hν₀_le1
  have hc_tp : p.c = PartI.trainPeriod 2 p.ν := by
    rw [hc]
    unfold PartI.trainPeriod
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg p.ν_pos.le, Real.rpow_natCast]
  have hBase_p :
      RapidProf (Jet.fluctFam p.ν p.c p.train) ∧
      RapidProf (Jet.presFam p.ν p.c p.train) ∧
      RapidProf (Jet.A2.stressFam p.ν p.c p.train) ∧
      EvRapidProf (fun M => remFam M p.ν p.c p.train) := by
    have hgen : ∀ (c : ℝ) (tr : UnforcedLeray.B0140.TrainSol p.ν c),
        c = PartI.trainPeriod 2 p.ν → IsBUCTrain tr →
        RapidProf (Jet.fluctFam p.ν c tr) ∧
        RapidProf (Jet.presFam p.ν c tr) ∧
        RapidProf (Jet.A2.stressFam p.ν c tr) ∧
        EvRapidProf (fun M => remFam M p.ν c tr) := by
      rintro _ tr rfl htr'
      exact HBase p.ν p.ν_pos hν.le tr htr'
    exact hgen p.c p.train hc_tp htr
  obtain ⟨hFl, hPr, hSt, hRm⟩ := hBase_p
  obtain ⟨hFA1, hFB1, hCA2, hFB2, hFB3, hRB1, hRB3, hRA1, hRB2⟩ :=
    all_nine_blocks_from_base p.ν_pos hν1 p.c_pos p.train htr hFl hPr hSt hRm
  obtain ⟨M₁, hM₁⟩ := hRB1 m w K
  obtain ⟨M₂, hM₂⟩ := hRB3 m w K
  obtain ⟨M₃, hM₃⟩ := hRA1 m w K
  obtain ⟨M₄, hM₄⟩ := hRB2 m w K
  set M : ℕ := max (max M₁ M₂) (max M₃ M₄)
  have hle1 : M₁ ≤ M := (le_max_left M₁ M₂).trans (le_max_left _ _)
  have hle2 : M₂ ≤ M := (le_max_right M₁ M₂).trans (le_max_left _ _)
  have hle3 : M₃ ≤ M := (le_max_left M₃ M₄).trans (le_max_right _ _)
  have hle4 : M₄ ≤ M := (le_max_right M₃ M₄).trans (le_max_right _ _)
  have h_rad : WtdProfJet m w (-(K : ℝ)) (f_rem_rad p M) :=
    ((((hM₁ M hle1).const_mul (ringEps p.R ^ 2)).add
      ((hM₃ M hle3).const_mul (ringEps p.R))).add
      ((hFA1 m w K).const_mul (ringEps p.R))).add
      ((hFB1 m w K).const_mul (ringEps p.R ^ 2))
  have h_ax : WtdProfJet m w (-(K : ℝ)) (f_rem_ax p M) :=
    (((((hM₂ M hle2).const_mul (ringEps p.R ^ 3)).add
      ((hM₄ M hle4).const_mul (ringEps p.R ^ 2))).add
      ((hCA2 m w K).const_mul (ringEps p.R))).add
      ((hFB2 m w K).const_mul (ringEps p.R ^ 2))).add
      ((hFB3 m w K).const_mul (ringEps p.R ^ 3))
  exact ⟨M, merid_chartSwap_jet_of_wtdProfJet h_rad h_ax⟩

end UnforcedLeray.Short.IIb.RawResidualIteratedLateTailAux
