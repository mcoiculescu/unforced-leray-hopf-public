import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecay.PostOverlapAgeDeriv.VelFluctHigherStep
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.OscMeanLap
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord

/-!
# `PartI:T22/2/2` (`PressureHigherStep.lean`): higher-age post-overlap pressure step

Source of record: `the November 2 reference manuscript`, lines 439–446 and 523–526.

Proves `trainPostOverlapPressureHigherStep_proof : TrainPostOverlapPressureHigherStep`:
given `hTails : TrainStreamVelocityPressureTails`, `hIH : ∀ r ≤ ℓ, TrainPostOverlapVelPressOrderSup r`,
and the age-`(ℓ + 1)` velocity-fluctuation bound `hV_succ`, bounds `wSupNorm 0 (ageJet (ℓ + 1) j tr.p s)`
on `s ≥ B0146.overlapAge ν c` by decomposing each word derivative `B0151.derivWord w (∂_s^{ℓ+1} p)`
into its horizontal mean (via `\bar p = -\overline{v₂²}`) and its horizontal oscillation
(via `-Δ p = poissonSource v`), where every term in both `v₂²` and `poissonSource v` retains at least
one factor of `v_fluct` of age order `≤ ℓ + 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet jap)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm)
open PartI_T22_2_1

namespace PartI_T22_2_2

/-! ### 1. Word-derivative (`B0151.derivWord`) and jointly smooth (`SmR`) calculus -/

theorem partialQ_add {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : Plane) :
    Cyl.partialQ (fun w => f w + g w) z = Cyl.partialQ f z + Cyl.partialQ g z := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  exact ((Cyl.hasDerivAt_sliceQ hfd z.1 z.2).add (Cyl.hasDerivAt_sliceQ hgd z.1 z.2)).deriv

theorem partialEta_add {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : Plane) :
    Cyl.partialEta (fun w => f w + g w) z = Cyl.partialEta f z + Cyl.partialEta g z :=
  cpMS_partialEta_add (hf.differentiable (by simp)) (hg.differentiable (by simp)) z

theorem partialQ_neg (f : Plane → ℝ) (z : Plane) :
    Cyl.partialQ (fun w => -f w) z = -Cyl.partialQ f z := by
  obtain ⟨x, y⟩ := z
  show deriv (fun q => -f (q, y)) x = -deriv (fun q => f (q, y)) x
  exact deriv.neg

theorem partialEta_neg (f : Plane → ℝ) (z : Plane) :
    Cyl.partialEta (fun w => -f w) z = -Cyl.partialEta f z :=
  cpMS_partialEta_neg f z

theorem derivWord_add {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ∀ (w : List Bool) (z : Plane),
      B0151.derivWord w (fun x => f x + g x) z =
        B0151.derivWord w f z + B0151.derivWord w g z
  | [], _ => rfl
  | true :: w, z => by
    have hfun : B0151.derivWord w (fun x => f x + g x) =
        fun x => B0151.derivWord w f x + B0151.derivWord w g x :=
      funext (derivWord_add hf hg w)
    change Cyl.partialQ (B0151.derivWord w (fun x => f x + g x)) z =
      Cyl.partialQ (B0151.derivWord w f) z + Cyl.partialQ (B0151.derivWord w g) z
    rw [hfun]
    exact partialQ_add (B0151.contDiff_derivWord hf w) (B0151.contDiff_derivWord hg w) z
  | false :: w, z => by
    have hfun : B0151.derivWord w (fun x => f x + g x) =
        fun x => B0151.derivWord w f x + B0151.derivWord w g x :=
      funext (derivWord_add hf hg w)
    change Cyl.partialEta (B0151.derivWord w (fun x => f x + g x)) z =
      Cyl.partialEta (B0151.derivWord w f) z + Cyl.partialEta (B0151.derivWord w g) z
    rw [hfun]
    exact partialEta_add (B0151.contDiff_derivWord hf w) (B0151.contDiff_derivWord hg w) z

theorem derivWord_neg (f : Plane → ℝ) :
    ∀ (w : List Bool) (z : Plane),
      B0151.derivWord w (fun x => -f x) z = -B0151.derivWord w f z
  | [], _ => rfl
  | true :: w, z => by
    have hfun : B0151.derivWord w (fun x => -f x) = fun x => -B0151.derivWord w f x :=
      funext (derivWord_neg f w)
    change Cyl.partialQ (B0151.derivWord w (fun x => -f x)) z =
      -Cyl.partialQ (B0151.derivWord w f) z
    rw [hfun]
    exact partialQ_neg (B0151.derivWord w f) z
  | false :: w, z => by
    have hfun : B0151.derivWord w (fun x => -f x) = fun x => -B0151.derivWord w f x :=
      funext (derivWord_neg f w)
    change Cyl.partialEta (B0151.derivWord w (fun x => -f x)) z =
      -Cyl.partialEta (B0151.derivWord w f) z
    rw [hfun]
    exact partialEta_neg (B0151.derivWord w f) z

theorem derivWord_partialQ_comm {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ w : List Bool, Cyl.partialQ (B0151.derivWord w f) = B0151.derivWord w (Cyl.partialQ f)
  | [] => rfl
  | true :: w => by
    funext z
    change Cyl.partialQ (Cyl.partialQ (B0151.derivWord w f)) z =
      Cyl.partialQ (B0151.derivWord w (Cyl.partialQ f)) z
    rw [derivWord_partialQ_comm hf w]
  | false :: w => by
    funext z
    change GaussianVortex.partialX (GaussianVortex.partialY (B0151.derivWord w f)) z =
      GaussianVortex.partialY (B0151.derivWord w (Cyl.partialQ f)) z
    rw [B0151.partialX_partialY_comm ((B0151.contDiff_derivWord hf w).of_le (by simp)) z,
      ← derivWord_partialQ_comm hf w]
    rfl

theorem derivWord_partialEta_comm {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ w : List Bool, Cyl.partialEta (B0151.derivWord w f) = B0151.derivWord w (Cyl.partialEta f)
  | [] => rfl
  | true :: w => by
    funext z
    change GaussianVortex.partialY (GaussianVortex.partialX (B0151.derivWord w f)) z =
      GaussianVortex.partialX (B0151.derivWord w (Cyl.partialEta f)) z
    rw [← B0151.partialX_partialY_comm ((B0151.contDiff_derivWord hf w).of_le (by simp)) z,
      ← derivWord_partialEta_comm hf w]
    rfl
  | false :: w => by
    funext z
    change Cyl.partialEta (Cyl.partialEta (B0151.derivWord w f)) z =
      Cyl.partialEta (B0151.derivWord w (Cyl.partialEta f)) z
    rw [derivWord_partialEta_comm hf w]

theorem derivWord_lapS_comm {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (w : List Bool) (z : Plane) :
    Train.lapS (B0151.derivWord w f) z = B0151.derivWord w (Train.lapS f) z := by
  have hQ1 : ContDiff ℝ ∞ (Cyl.partialQ f) := B0151.contDiff_partialX_infty hf
  have hQ2 : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialQ f)) := B0151.contDiff_partialX_infty hQ1
  have hE1 : ContDiff ℝ ∞ (Cyl.partialEta f) := B0151.contDiff_partialY_infty hf
  have hE2 : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialEta f)) := B0151.contDiff_partialY_infty hE1
  unfold Train.lapS
  rw [derivWord_partialQ_comm hf w, derivWord_partialQ_comm hQ1 w,
    derivWord_partialEta_comm hf w, derivWord_partialEta_comm hE1 w,
    ← derivWord_add hQ2 hE2 w z]

theorem smR_iteratedDeriv {F : ℝ → Plane → ℝ}
    (hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) :
    PartI_T20.SmR (fun x : ℝ × Plane => iteratedDeriv ℓ (fun r => F r x.2) x.1) :=
  (PartI_T20.smR_DtR hF ℓ).congr fun ⟨_t, z⟩ hx =>
    PartI_T20.iteratedDeriv_slice_eq_DtR hF ℓ hx.1 z

theorem contDiff_iteratedDeriv_slice {F : ℝ → Plane → ℝ}
    (hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ (fun r => F r z') t) :=
  PartI_T20.contDiff_slice_of_smR
    (F := fun t' z' => iteratedDeriv ℓ (fun r => F r z') t') (smR_iteratedDeriv hF ℓ) ht

theorem isPeriodic_derivWord {c : ℝ} {f : Plane → ℝ} (hf : Cyl.IsPeriodic c f) (w : List Bool) :
    Cyl.IsPeriodic c (B0151.derivWord w f) := fun ⟨q, η⟩ =>
  B0151.periodic_derivWord (fun q' η' => hf (q', η')) w q η

theorem abs_derivWord_iteratedDeriv_le_ageJet {F : ℝ → Plane → ℝ}
    (hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2))
    (ℓ k : ℕ) {w : List Bool} (hw : w.length = k) {t : ℝ} (ht : 0 < t) (z : Plane) :
    |B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => F r z') t) z| ≤
      ‖ageJet ℓ k F t z‖ := by
  have hg : ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ (fun r => F r z') t) :=
    contDiff_iteratedDeriv_slice hF ℓ ht
  exact (cylJetWord_proof (fun z' => iteratedDeriv ℓ (fun r => F r z') t) hg k z).1 w hw

theorem isPeriodic_iteratedDeriv {c : ℝ} {F : ℝ → Plane → ℝ}
    (hper : ∀ r : ℝ, 0 < r → Cyl.IsPeriodic c (F r)) (ℓ : ℕ) {t : ℝ} (ht : 0 < t) :
    Cyl.IsPeriodic c (fun z : Plane => iteratedDeriv ℓ (fun r => F r z) t) := by
  intro z
  have hev : (fun r => F r (z.1 + c, z.2)) =ᶠ[𝓝 t] fun r => F r z := by
    filter_upwards [Ioi_mem_nhds ht] with r hr using hper r hr z
  exact hev.iteratedDeriv_eq ℓ

theorem smR_poissonSource {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) :
    PartI_T20.SmR (fun x : ℝ × Plane => poissonSource (V x.1) x.2) := by
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 0) hsm_v0
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 1) hsm_v1
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 0) hsm_v0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 1) hsm_v1
  unfold poissonSource
  exact ((hQ0.pow 2).add (contDiffOn_const.mul (hQ1.mul hE0))).add (hE1.pow 2)

/-! ### 2. Horizontal mean and oscillation identities for `B0151.derivWord w (P_ℓ s)` -/

theorem hmean_partialQ_zero {c : ℝ} {f : Plane → ℝ} (hc : 0 < c)
    (hf : ContDiff ℝ 1 f) (hper : Cyl.IsPeriodic c f) (η : ℝ) :
    hmean c (Cyl.partialQ f) η = 0 := by
  unfold hmean
  rw [oscMeanLap_integral_partialQ_zero hc hf hper η, smul_zero]

theorem hmean_derivWord_neg_eq {c : ℝ} (hc : 0 < c) {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Cyl.IsPeriodic c f) (hgp : Cyl.IsPeriodic c g)
    (hfg : ∀ η : ℝ, hmean c f η = -hmean c g η) :
    ∀ (w : List Bool) (η : ℝ),
      hmean c (B0151.derivWord w f) η = -hmean c (B0151.derivWord w g) η
  | [], η => hfg η
  | true :: w, η => by
    have hwf : ContDiff ℝ 1 (B0151.derivWord w f) :=
      (B0151.contDiff_derivWord hf w).of_le (by simp)
    have hwg : ContDiff ℝ 1 (B0151.derivWord w g) :=
      (B0151.contDiff_derivWord hg w).of_le (by simp)
    have hpf : Cyl.IsPeriodic c (B0151.derivWord w f) := isPeriodic_derivWord hfp w
    have hpg : Cyl.IsPeriodic c (B0151.derivWord w g) := isPeriodic_derivWord hgp w
    change hmean c (Cyl.partialQ (B0151.derivWord w f)) η =
      -hmean c (Cyl.partialQ (B0151.derivWord w g)) η
    rw [hmean_partialQ_zero hc hwf hpf η, hmean_partialQ_zero hc hwg hpg η, neg_zero]
  | false :: w, η => by
    have hwf : ContDiff ℝ 1 (B0151.derivWord w f) :=
      (B0151.contDiff_derivWord hf w).of_le (by simp)
    have hwg : ContDiff ℝ 1 (B0151.derivWord w g) :=
      (B0151.contDiff_derivWord hg w).of_le (by simp)
    have hih : hmean c (B0151.derivWord w f) = fun e => -hmean c (B0151.derivWord w g) e :=
      funext (hmean_derivWord_neg_eq hc hf hg hfp hgp hfg w)
    change hmean c (Cyl.partialEta (B0151.derivWord w f)) η =
      -hmean c (Cyl.partialEta (B0151.derivWord w g)) η
    rw [← congrFun (cpH2_deriv_hmean hwf) η, ← congrFun (cpH2_deriv_hmean hwg) η, hih]
    exact deriv.neg

theorem train_hmean_p_eq_neg_v1_sq {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    hmean c (tr.p r) η = -hmean c (fun z : Plane => tr.v r z 1 ^ 2) η := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hr1 : 0 < r + 1 := by linarith
  have hmem : r ∈ Icc (0 : ℝ) (r + 1) := ⟨hr.le, by linarith⟩
  have hcl : IsClassicalOn ν c (r + 1) tr.v tr.p := trainSol_isClassicalOn tr (r + 1)
  have hlap : ∀ z : Plane, Train.lapS (tr.p r) z = -poissonSource (tr.v r) z :=
    slicePoisson ν c (r + 1) tr.v tr.p hν hc1 hr1 hcl r hmem
  have hv_dec : Tendsto (tr.v r) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) :=
    velocityDecayOfEnergy ν c (r + 1) tr.v tr.p hν hc1 hr1 hcl (htr (r + 1) hr1.le) r hmem
  have hp_dec : Tendsto (tr.p r) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) :=
    tr.isTrain.pressure_decay r hr.le
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hu : ContDiff ℝ ∞ (tr.v r) :=
    (contDiffOn_univ.1 (hsm_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => mem_UU hr)))
  have hq : ContDiff ℝ 2 (tr.p r) :=
    (PartI_T20.contDiff_slice_of_smR hsm_p hr).of_le (by simp)
  have hup : Cyl.IsPeriodic c (tr.v r) := tr.isTrain.periodic_v r hr.le
  have hqp : Cyl.IsPeriodic c (tr.p r) := tr.isTrain.periodic_p r hr.le
  have hdiv : ∀ z : Plane, Cyl.divergence (tr.v r) z = 0 := tr.isTrain.solenoidal r hr.le
  let g : Plane → ℝ := fun z => tr.v r z 1 ^ 2
  have hproj : ContDiff ℝ ∞ (fun z : Plane => tr.v r z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hg2 : ContDiff ℝ 2 g := (hproj.pow 2).of_le (by simp)
  obtain ⟨hqC, hq''⟩ := cylPoisHmeanC2 c (tr.p r) hc hq
  obtain ⟨hgC, hg''⟩ := cylPoisHmeanC2 c g hc hg2
  have hFC : ContDiff ℝ 2 (fun e => hmean c (tr.p r) e + hmean c g e) := hqC.add hgC
  have hsrc : ∀ e : ℝ,
      hmean c (poissonSource (tr.v r)) e = hmean c (Cyl.partialEta (Cyl.partialEta g)) e :=
    cylPoisMeanSource c (tr.v r) hc hu hup hdiv
  have hlapfun : Train.lapS (tr.p r) = fun z => -poissonSource (tr.v r) z := funext hlap
  have hneg : ∀ e : ℝ, hmean c (Train.lapS (tr.p r)) e = -hmean c (poissonSource (tr.v r)) e := by
    intro e
    rw [hlapfun]
    unfold hmean
    simp only [integral_neg, smul_neg]
  have hF2 : ∀ e : ℝ, deriv (deriv (fun e => hmean c (tr.p r) e + hmean c g e)) e = 0 := by
    intro e
    have hd : deriv (fun e => hmean c (tr.p r) e + hmean c g e) =
        fun e => deriv (hmean c (tr.p r)) e + deriv (hmean c g) e := by
      funext e'
      exact deriv_add (hqC.differentiable (by norm_num) e') (hgC.differentiable (by norm_num) e')
    have hsum : deriv (fun e => deriv (hmean c (tr.p r)) e + deriv (hmean c g) e) e =
        deriv (deriv (hmean c (tr.p r))) e + deriv (deriv (hmean c g)) e :=
      deriv_add (cylpDifferentiableDeriv hqC e) (cylpDifferentiableDeriv hgC e)
    rw [hd, hsum, hq'' e, hg'' e, ← cylPoisHmeanLap c (tr.p r) hc hq hqp e, hneg e, ← hsrc e]
    ring
  have hq_dec : Tendsto (hmean c (tr.p r)) (cocompact ℝ) (𝓝 0) :=
    cylpTendstoCocompact (gg_hmean_tendsto hc hp_dec)
  have hu1 : Tendsto g (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have h := ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.tendsto 0).comp hv_dec
    simpa [g] using h.pow 2
  have hg_dec : Tendsto (hmean c g) (cocompact ℝ) (𝓝 0) :=
    cylpTendstoCocompact (gg_hmean_tendsto hc hu1)
  have hF_dec : Tendsto (fun e => hmean c (tr.p r) e + hmean c g e) (cocompact ℝ) (𝓝 0) := by
    simpa using hq_dec.add hg_dec
  have hzero := cylPoisAffineZero _ hFC hF2 hF_dec η
  linarith

theorem oscLinear_explicit {c K : ℝ} (hc : 0 < c) (hK0 : 0 ≤ K) {q : Plane → ℝ}
    (hq : ContDiff ℝ 2 q) (hqp : Cyl.IsPeriodic c q)
    (hgrad : ∃ L : ℝ, ∀ z, |Cyl.partialQ q z| ≤ L ∧ |Cyl.partialEta q z| ≤ L)
    (hlap : ∀ z, |Train.lapS q z| ≤ K) (z : Plane) :
    |q z - hmean c q z.2| ≤
      (K * c ^ 2 / (2 * Real.pi ^ 2)) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  let a : ℝ := K * c ^ 2 / (2 * Real.pi ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨C, hC⟩ := pbGradToGrowth c q hc (hq.of_le (by norm_num)) hqp hgrad
  have hf2 : ContDiff ℝ 2 (fun w : Plane => ((q w : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hfper : Cyl.IsPeriodic c (fun w : Plane => ((q w : ℝ) : ℂ)) := fun w => by
    simp only [hqp w]
  have hsrc : ∀ w : Plane, ‖((Train.lapS q w : ℝ) : ℂ)‖ ≤ K := fun w => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hlap w
  have hgrow : ∀ (n : ℤ) (η : ℝ),
      ‖Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) η‖ ≤ C * (1 + |η|) := by
    intro n η
    have hslice : ∀ w : Plane,
        ‖(fun w : Plane => ((q (w.1, η) : ℝ) : ℂ)) w‖ ≤ C * (1 + |η|) := fun w => by
      show ‖((q (w.1, η) : ℝ) : ℂ)‖ ≤ C * (1 + |η|)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hC (w.1, η)
    exact (cylPoisQModeEstimates c hc n (fun w : Plane => ((q (w.1, η) : ℝ) : ℂ))).1 _ hslice η
  have hmode : ∀ (η : ℝ) (n : ℤ), n ≠ 0 →
      ‖Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) η‖ ≤ a / (n : ℝ) ^ 2 := by
    intro η n hn
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hc0 : c ≠ 0 := hc.ne'
    let lam : ℝ := 2 * Real.pi * |(n : ℝ)| / c
    have hlam : 0 < lam := by
      dsimp [lam]
      have : 0 < |(n : ℝ)| := abs_pos.2 hn'
      positivity
    have hlam2 : lam ^ 2 = (2 * Real.pi * n / c) ^ 2 := by
      dsimp [lam]
      rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
      ring
    obtain ⟨hm2, hm''⟩ := cylPoisModeC2 c hc n _ hf2
    have hlap_mode : ∀ e, ‖deriv (deriv (Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)))) e
        - ((lam ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) e‖
          ≤ K := by
      intro e
      have hL := cylPoisModeLaplace c hc n q hq hqp hn e
      have hEq : deriv (deriv (Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)))) e
          - ((lam ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) e
          = Cyl.qMode c hc n (fun w => ((Train.lapS q w : ℝ) : ℂ)) e := by
        rw [hm'' e, hL, hlam2]
      rw [hEq]
      exact (cylPoisQModeEstimates c hc n _).1 K hsrc e
    have hbound := pbMaxPrincipleLinear _ lam K hm2 hlam hlap_mode ⟨C, fun e => hgrow n e⟩ η
    refine hbound.trans (le_of_eq ?_)
    rw [hlam2]
    dsimp [a]
    field_simp
  have hA : Summable (fun n : ℤ => a / (n : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    refine (h.mul_left a).congr (fun n => ?_)
    rw [mul_one_div]
  have hA0 : ∀ n : ℤ, 0 ≤ a / (n : ℝ) ^ 2 := fun n => div_nonneg ha (sq_nonneg _)
  have hres := cylPoisFourierPointwise c hc (fun w : Plane => ((q w : ℝ) : ℂ))
    (fun n : ℤ => a / (n : ℝ) ^ 2) z.2 hf2.continuous hfper hA hA0 (fun n hn => hmode z.2 n hn) z.1
  have hsum : ∑' n : ℤ, a / (n : ℝ) ^ 2 = a * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by rw [mul_one_div])
  have hq0m : Cyl.qMode c hc 0 (fun w : Plane => ((q w : ℝ) : ℂ)) z.2
      = ((hmean c q z.2 : ℝ) : ℂ) := by
    rw [Cyl.qMode_zero hc]
    exact cylPoisQAvgReal c q z.2
  rw [hq0m, hsum] at hres
  calc |q z - hmean c q z.2| = ‖((q z : ℝ) : ℂ) - ((hmean c q z.2 : ℝ) : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ a * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := hres

/-! ### 3. Bilinear fluctuation bounds for `poissonSource (tr.v r)` and `B0151.derivWord w P_ℓ` -/

theorem norm_ageJet_poissonSource_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M_F)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s z‖ ≤ M_V) :
    ‖ageJet ℓ j (fun r w => poissonSource (tr.v r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + j) * M_F * M_V := by
  let V : ℝ → Plane → Vec := tr.v
  let VF : ℝ → Plane → Vec := fun t => hfluct c (tr.v t)
  have hV : Sm (fun x : ℝ × Plane => V x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hVF : Sm (fun x : ℝ × Plane => VF x.1 x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_vf0 : PartI_T20.SmR (fun x : ℝ × Plane => VF x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hVF
  have hsm_vf1 : PartI_T20.SmR (fun x : ℝ × Plane => VF x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hVF
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 0) hsm_v0
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 1) hsm_v1
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 0) hsm_v0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 1) hsm_v1
  let P₁ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 0) w * Cyl.partialQ (fun y => V r y 0) w
  let P₂ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 0) w
  let P₃ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialEta (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 1) w
  have hsm₁ : PartI_T20.SmR (fun x : ℝ × Plane => P₁ x.1 x.2) := hQ0.mul hQ0
  have hsm₂ : PartI_T20.SmR (fun x : ℝ × Plane => P₂ x.1 x.2) := hQ1.mul hE0
  have hsm₃ : PartI_T20.SmR (fun x : ℝ × Plane => P₃ x.1 x.2) := hE1.mul hE1
  have hfun : (fun r w => poissonSource (V r) w) =
      fun r w => (P₁ r w + (P₂ r w + P₂ r w)) + P₃ r w := by
    funext r w
    unfold poissonSource
    dsimp [P₁, P₂, P₃]
    ring
  have hadd1 := PartI_T20.ageJet_add (fun r w => P₁ r w + (P₂ r w + P₂ r w)) P₃
    (hsm₁.add (hsm₂.add hsm₂)) hsm₃ hs ℓ j z
  have hadd2 := PartI_T20.ageJet_add P₁ (fun r w => P₂ r w + P₂ r w)
    hsm₁ (hsm₂.add hsm₂) hs ℓ j z
  have hadd3 := PartI_T20.ageJet_add P₂ P₂ hsm₂ hsm₂ hs ℓ j z
  have hQ0_eq : (fun t w => Cyl.partialQ (fun y => V t y 0) w) =
      fun t w => Cyl.partialQ (fun y => VF t y 0) w :=
    funext fun t => funext fun w => partialQ_train_v_eq_fluct tr t 0 w
  have hQ1_eq : (fun t w => Cyl.partialQ (fun y => V t y 1) w) =
      fun t w => Cyl.partialQ (fun y => VF t y 1) w :=
    funext fun t => funext fun w => partialQ_train_v_eq_fluct tr t 1 w
  have hQ0_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M_F := by
    intro r hr i hi
    rw [hQ0_eq]
    exact ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => VF t w 0) hsm_vf0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hVF 0 r (i + 1) hs z)).trans (hF_bd r hr (i + 1) (by omega))
  have hQ1_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 1) w) s z‖ ≤ M_F := by
    intro r hr i hi
    rw [hQ1_eq]
    exact ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => VF t w 1) hsm_vf1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hVF 1 r (i + 1) hs z)).trans (hF_bd r hr (i + 1) (by omega))
  have hE1_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M_F := by
    intro r hr i hi
    calc ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖
        ≤ ‖ageJet r (i + 1) (fun t w => V t w 1) s z‖ :=
          PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z
      _ = ‖ageJet r (i + 1) (fun t w => VF t w 1) s z‖ := by
          rw [ageJet_train_v_one_eq_fluct hν hc tr r (i + 1) hs z]
      _ ≤ ‖ageJet r (i + 1) VF s z‖ :=
          PartI_T20.norm_ageJet_vec_proj_le hVF 1 r (i + 1) hs z
      _ ≤ M_F := hF_bd r hr (i + 1) (by omega)
  have hQ0_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hE0_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 0) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hE1_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 1 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hb₁ := PartI_T20.norm_ageJet_mul_le hQ0 hQ0 ℓ j hs hMF hMV z hQ0_F_bd hQ0_V_bd
  have hb₂ := PartI_T20.norm_ageJet_mul_le hQ1 hE0 ℓ j hs hMF hMV z hQ1_F_bd hE0_V_bd
  have hb₃ := PartI_T20.norm_ageJet_mul_le hE1 hE1 ℓ j hs hMF hMV z hE1_F_bd hE1_V_bd
  rw [hfun, hadd1, hadd2, hadd3]
  have htri1 := norm_add_le
    (ageJet ℓ j P₁ s z + (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)) (ageJet ℓ j P₃ s z)
  have htri2 := norm_add_le (ageJet ℓ j P₁ s z) (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)
  have htri3 := norm_add_le (ageJet ℓ j P₂ s z) (ageJet ℓ j P₂ s z)
  linarith

theorem abs_hmean_derivWord_p_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ k : ℕ) {w : List Bool} (hw : w.length = k) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s w'‖ ≤ M_F)
    (hV_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k, ‖ageJet r i tr.v s w'‖ ≤ M_V) :
    |hmean c (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z.2| ≤
      (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hVF : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_sq : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) := by
    have : (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) =
        fun x : ℝ × Plane => tr.v x.1 x.2 1 * tr.v x.1 x.2 1 :=
      funext fun _ => sq _
    rw [this]
    exact hsm_v1.mul hsm_v1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  let G_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.v r z' 1 ^ 2) s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hG_sm : ContDiff ℝ ∞ G_ℓ :=
    contDiff_iteratedDeriv_slice (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs
  have hP_per : Cyl.IsPeriodic c P_ℓ :=
    isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs
  have hG_per : Cyl.IsPeriodic c G_ℓ := by
    refine isPeriodic_iteratedDeriv (fun r hr z' => ?_) ℓ hs
    exact congrArg (fun v : Vec => v 1 ^ 2) (tr.isTrain.periodic_v r hr.le z')
  have hmean_eq : ∀ η : ℝ, hmean c P_ℓ η = -hmean c G_ℓ η := by
    intro η
    rw [← iteratedDeriv_hmean_scalar_eq hc hsm_p ℓ hs η,
      ← iteratedDeriv_hmean_scalar_eq hc (f := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs η,
      ← iteratedDeriv_neg]
    have hev : (fun r => hmean c (tr.p r) η) =ᶠ[𝓝 s]
        fun r => -hmean c (fun z' : Plane => tr.v r z' 1 ^ 2) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using
        train_hmean_p_eq_neg_v1_sq hν hc1 tr htr hr η
    exact hev.iteratedDeriv_eq ℓ
  have hword_eq := hmean_derivWord_neg_eq hc hP_sm hG_sm hP_per hG_per hmean_eq w z.2
  rw [hword_eq, abs_neg]
  refine cylpHmeanAbsLe hc (fun w' => ?_) z.2
  have hsq_fn : (fun r (z' : Plane) => tr.v r z' 1 ^ 2) =
      fun r z' => tr.v r z' 1 * tr.v r z' 1 := by
    funext r z'; exact sq _
  calc |B0151.derivWord w G_ℓ w'|
      ≤ ‖ageJet ℓ k (fun r z' => tr.v r z' 1 ^ 2) s w'‖ :=
        abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => tr.v r z' 1 ^ 2)
          hsm_sq ℓ k hw hs w'
    _ = ‖ageJet ℓ k (fun r z' => tr.v r z' 1 * tr.v r z' 1) s w'‖ := by rw [hsq_fn]
    _ ≤ (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
        refine PartI_T20.norm_ageJet_mul_le
          (A := fun r z' => tr.v r z' 1) (B := fun r z' => tr.v r z' 1)
          hsm_v1 hsm_v1 ℓ k hs hMF hMV w' (fun r hr i hi => ?_) (fun r hr i hi => ?_)
        · rw [ageJet_train_v_one_eq_fluct hν hc tr r i hs w']
          exact (PartI_T20.norm_ageJet_vec_proj_le hVF 1 r i hs w').trans (hF_bd w' r hr i hi)
        · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs w').trans (hV_bd w' r hr i hi)

theorem abs_lapS_derivWord_p_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M_F)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v s z‖ ≤ M_V) :
    |Train.lapS (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z| ≤
      4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_src : PartI_T20.SmR (fun x : ℝ × Plane => poissonSource (tr.v x.1) x.2) :=
    smR_poissonSource hsm_v
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hlap_P : Train.lapS P_ℓ =
      fun z' => -iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') s := by
    funext z'
    have h1 := PartI_T20.iteratedDeriv_mul_lapS_eq hsm_p 1 ℓ hs z'
    simp only [one_mul] at h1
    rw [← h1, ← iteratedDeriv_neg]
    have hev : (fun r => Train.lapS (tr.p r) z') =ᶠ[𝓝 s]
        fun r => -poissonSource (tr.v r) z' := by
      filter_upwards [Ioi_mem_nhds hs] with r (hr : 0 < r)
      exact slicePoisson ν c (r + 1) tr.v tr.p hν hc1 (by linarith)
        (trainSol_isClassicalOn tr (r + 1)) r ⟨hr.le, by linarith⟩ z'
    exact hev.iteratedDeriv_eq ℓ
  rw [derivWord_lapS_comm hP_sm w z, hlap_P, derivWord_neg _ w z, abs_neg]
  calc |B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') s) z|
      ≤ ‖ageJet ℓ k (fun r z' => poissonSource (tr.v r) z') s z‖ :=
        abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => poissonSource (tr.v r) z')
          hsm_src ℓ k hw hs z
    _ ≤ 4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V :=
        norm_ageJet_poissonSource_fluct_le hν hc hMF hMV tr ℓ k hs z hF_bd hV_bd

theorem abs_osc_derivWord_p_fluct_le {ν c M_F M_V L_p : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hp_grad : ∀ z' : Plane, ‖ageJet ℓ (k + 1) tr.p s z'‖ ≤ L_p)
    (hF_bd : ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s z'‖ ≤ M_F)
    (hV_bd : ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v s z'‖ ≤ M_V) :
    let Q_s : Plane → ℝ := B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)
    let K_src : ℝ := 4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V
    |Q_s z - hmean c Q_s z.2| ≤
      (K_src * c ^ 2 / (2 * Real.pi ^ 2)) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  intro Q_s K_src
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hK_nn : 0 ≤ K_src := by dsimp [K_src]; positivity
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hQ_C2 : ContDiff ℝ 2 Q_s := (B0151.contDiff_derivWord hP_sm w).of_le (by simp)
  have hQ_per : Cyl.IsPeriodic c Q_s :=
    isPeriodic_derivWord
      (isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs) w
  have hgrad : ∃ L : ℝ, ∀ y : Plane, |Cyl.partialQ Q_s y| ≤ L ∧ |Cyl.partialEta Q_s y| ≤ L := by
    refine ⟨L_p, fun y => ⟨?_, ?_⟩⟩
    · have hlen_t : (true :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (true :: w) P_ℓ y| ≤ L_p
      exact (abs_derivWord_iteratedDeriv_le_ageJet hsm_p ℓ (k + 1) hlen_t hs y).trans
        (hp_grad y)
    · have hlen_f : (false :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (false :: w) P_ℓ y| ≤ L_p
      exact (abs_derivWord_iteratedDeriv_le_ageJet hsm_p ℓ (k + 1) hlen_f hs y).trans
        (hp_grad y)
  have hlap : ∀ y : Plane, |Train.lapS Q_s y| ≤ K_src := fun y =>
    abs_lapS_derivWord_p_fluct_le hν hc1 hMF hMV tr ℓ k hw hs y (hF_bd y) (hV_bd y)
  exact oscLinear_explicit hc hK_nn hQ_C2 hQ_per hgrad hlap z

/-! ### 4. Uniform rectangle bound for `v_fluct` across `r ≤ ℓ + 1` and `i ≤ K` -/

theorem uniform_velFluct_exp_row_at (L : ℕ)
    (hV_L : ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
      0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            let c := trainPeriod ρ ν
            let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
            wSupNorm 0 (ageJet L j v_fluct s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))))
    {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    ∀ K : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            ∀ z : Plane, ∀ i ≤ K,
              let c := trainPeriod ρ ν
              ‖ageJet L i (fun t => hfluct c (tr.v t)) s z‖ ≤
                polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))
  | 0 => by
    obtain ⟨C, N, lam, ν₀, hC, hlam, hν₀, h0⟩ := hV_L ρ hρ 0
    refine ⟨C, N, lam, ν₀, hC, hlam, hν₀, fun ν hν hν_le tr htr s hs hsc z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    have hM : 0 ≤ polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
      unfold polyP; positivity
    exact norm_le_of_wSupNorm_zero_le hM (h0 ν hν hν_le tr htr s hs hsc) z
  | K + 1 => by
    obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hIH⟩ :=
      uniform_velFluct_exp_row_at L hV_L hρ K
    obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hK1⟩ := hV_L ρ hρ (K + 1)
    refine ⟨max C₁ C₂, max N₁ N₂, min lam₁ lam₂, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hsc z i hi
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hi with hiK | rfl
    · have hv := hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs hsc z i hiK
      exact hv.trans (polyP_exp_mono (ν := ν) (c := c) (s := s) C₁ (max C₁ C₂) lam₁ (min lam₁ lam₂)
        N₁ (max N₁ N₂) hC₁.le (le_max_left _ _) (le_max_left _ _) (min_le_left _ _) hν hc.le hs.le)
    · have hM₂ : 0 ≤ polyP C₂ N₂ ν c * Real.exp (-(lam₂ * ν * s / c ^ 2)) := by
        unfold polyP; positivity
      have hv := norm_le_of_wSupNorm_zero_le hM₂
        (hK1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs hsc) z
      exact hv.trans (polyP_exp_mono (ν := ν) (c := c) (s := s) C₂ (max C₁ C₂) lam₂ (min lam₁ lam₂)
        N₂ (max N₁ N₂) hC₂.le (le_max_right _ _) (le_max_right _ _) (min_le_right _ _) hν hc.le hs.le)

end PartI_T22_2_2

open PartI_T22_2_2 in
/-- **Higher-age pressure inductive step (`PartI:T22/2/2`)**:
proves `TrainPostOverlapPressureHigherStep`. -/
theorem trainPostOverlapPressureHigherStep_proof : TrainPostOverlapPressureHigherStep := by
  intro hTails _hVel0 _hSP0 _hOv ℓ hIH hV_succ ρ hρ j
  obtain ⟨C_V, N_V, ν_V, hC_V, hν_V, hV_rect⟩ :=
    uniform_vel_polyPS_rect hTails hρ (j + 1) (ℓ + 1)
  obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hFl_le⟩ :=
    uniform_velPress_exp_rect hIH hρ (j + 1)
  obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hFl_succ⟩ :=
    uniform_velFluct_exp_row_at (ℓ + 1) hV_succ hρ (j + 1)
  obtain ⟨C_P1, N_P1, ν_P1, hCP1, hνP1, hT_p⟩ := hTails.2.2 ρ hρ 0 (ℓ + 1) (j + 1)
  obtain ⟨νp, hνp, _hνp1, hp_asymp⟩ := trainPeriodAsymptotics_proof ρ hρ 1 one_pos
  let C_F : ℝ := max C₁ C₂
  let N_F : ℕ := max N₁ N₂
  let lam_F : ℝ := min lam₁ lam₂
  have hC_F : 0 < C_F := lt_max_of_lt_left hC₁
  have hlam_F : 0 < lam_F := lt_min hlam₁ hlam₂
  let K_abs : ℝ := (N_V.factorial : ℝ) * ((lam_F / 2) ^ N_V)⁻¹ * Real.exp (lam_F / 2)
  have hfac_pos : (0 : ℝ) < N_V.factorial := by exact_mod_cast N_V.factorial_pos
  have hK_abs : 0 < K_abs := by dsimp [K_abs]; positivity
  let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun _ => by positivity
  let C_out : ℝ :=
    (2 : ℝ) ^ (ℓ + 1 + 2 * j) * (C_V * C_F * K_abs) *
      (1 + (4 / (2 * Real.pi ^ 2)) * S_zeta)
  let N_out : ℕ := (4 * N_V + N_F) + 2
  let lam_out : ℝ := lam_F / 2
  let ν₀ : ℝ := min (min ν_V (min ν₁ ν₂)) (min ν_P1 (min νp 1))
  have hC_out : 0 < C_out := by dsimp [C_out]; positivity
  have hlam_out : 0 < lam_out := by dsimp [lam_out]; positivity
  have hν₀ : 0 < ν₀ :=
    lt_min (lt_min hν_V (lt_min hν₁ hν₂)) (lt_min hνP1 (lt_min hνp zero_lt_one))
  refine ⟨C_out, N_out, lam_out, ν₀, hC_out, hlam_out, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν_V_le : ν ≤ ν_V := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₁_le : ν ≤ ν₁ :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν₂_le : ν ≤ ν₂ :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν_P1_le : ν ≤ ν_P1 := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_p_le : ν ≤ νp :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hc1, _⟩ := hp_asymp ν hν hν_p_le
  let c := trainPeriod ρ ν
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ X := by dsimp [X]; linarith
  have hcX : c ≤ X := by dsimp [X]; linarith
  let M_V : ℝ := polyPS C_V N_V ν c s
  let M_F : ℝ := polyP C_F N_F ν c * Real.exp (-(lam_F * ν * s / c ^ 2))
  let L_p : ℝ := polyPS C_P1 N_P1 ν c s
  have hMV : 0 ≤ M_V := by dsimp [M_V]; unfold polyPS; positivity
  have hMF : 0 ≤ M_F := by dsimp [M_F]; unfold polyP; positivity
  have hLp_nn : 0 ≤ L_p := by dsimp [L_p]; unfold polyPS; positivity
  have hF_bd : ∀ z' : Plane, ∀ r ≤ ℓ + 1, ∀ i ≤ j + 1,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s z'‖ ≤ M_F := by
    intro z' r hr i hi
    rcases Nat.of_le_succ hr with hrL | rfl
    · have hv := (hFl_le ν hν hν₁_le tr htr s hs hsc z' r hrL i hi).1
      exact hv.trans (polyP_exp_mono C₁ C_F lam₁ lam_F N₁ N_F
        hC₁.le (le_max_left _ _) (le_max_left _ _) (min_le_left _ _) hν hc.le hs.le)
    · have hv := hFl_succ ν hν hν₂_le tr htr s hs hsc z' i hi
      exact hv.trans (polyP_exp_mono C₂ C_F lam₂ lam_F N₂ N_F
        hC₂.le (le_max_right _ _) (le_max_right _ _) (min_le_right _ _) hν hc.le hs.le)
  have hV_bd : ∀ z' : Plane, ∀ r ≤ ℓ + 1, ∀ i ≤ j + 1, ‖ageJet r i tr.v s z'‖ ≤ M_V :=
    fun z' r hr i hi => hV_rect ν hν hν_V_le tr htr s hs z' r hr i hi
  have hp_grad : ∀ z' : Plane, ‖ageJet (ℓ + 1) (j + 1) tr.p s z'‖ ≤ L_p := by
    intro z'
    have hsup := (hT_p ν hν hν_P1_le tr htr s hs).2.2.2.2.2
    exact norm_le_of_wSupNorm_zero_le hLp_nn hsup z'
  refine wSupNorm_zero_le_of_norm_le fun z => ?_
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_L : Plane → ℝ := fun z' => iteratedDeriv (ℓ + 1) (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_L := contDiff_iteratedDeriv_slice hsm_p (ℓ + 1) hs
  let B_word : ℝ :=
    (2 : ℝ) ^ (ℓ + 1 + j) * (M_V * M_F) * (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta)
  have hword_bd : ∀ w ∈ wordsOfLength j, |B0151.derivWord w P_L z| ≤ B_word := by
    intro w hw
    have hlen : w.length = j := by
      unfold wordsOfLength at hw
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hw
      simp
    have hmean_bd := abs_hmean_derivWord_p_fluct_le
      hν hc1 hMF hMV tr htr (ℓ + 1) j hlen hs z
      (fun w' r hr i hi => hF_bd w' r hr i (by omega))
      (fun w' r hr i hi => hV_bd w' r hr i (by omega))
    have hosc_bd := abs_osc_derivWord_p_fluct_le
      hν hc1 hMF hMV tr (ℓ + 1) j hlen hs z hp_grad hF_bd hV_bd
    have htri : |B0151.derivWord w P_L z| ≤
        |B0151.derivWord w P_L z - hmean c (B0151.derivWord w P_L) z.2| +
          |hmean c (B0151.derivWord w P_L) z.2| := by
      have := abs_add_le (B0151.derivWord w P_L z - hmean c (B0151.derivWord w P_L) z.2)
        (hmean c (B0151.derivWord w P_L) z.2)
      rwa [sub_add_cancel] at this
    calc |B0151.derivWord w P_L z|
        ≤ (4 * (2 : ℝ) ^ (ℓ + 1 + j) * M_F * M_V * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta +
            (2 : ℝ) ^ (ℓ + 1 + j) * M_F * M_V :=
          htri.trans (add_le_add hosc_bd hmean_bd)
      _ = B_word := by dsimp [B_word]; ring
  have hjet_word := (cylJetWord_proof P_L hP_sm j z).2
  have hcard_nat : (wordsOfLength j).card ≤ 2 ^ j := by
    unfold wordsOfLength
    exact Finset.card_image_le.trans (by simp)
  have hcard : ((wordsOfLength j).card : ℝ) ≤ (2 : ℝ) ^ j := by
    exact_mod_cast hcard_nat
  have hB_nn : 0 ≤ B_word := by dsimp [B_word]; positivity
  have hjet_le : ‖ageJet (ℓ + 1) j tr.p s z‖ ≤ (2 : ℝ) ^ j * B_word := by
    change ‖iteratedFDeriv ℝ j P_L z‖ ≤ _
    calc ‖iteratedFDeriv ℝ j P_L z‖
        ≤ ∑ w ∈ wordsOfLength j, |B0151.derivWord w P_L z| := hjet_word
      _ ≤ ∑ _w ∈ wordsOfLength j, B_word := Finset.sum_le_sum fun w hw => hword_bd w hw
      _ = ((wordsOfLength j).card : ℝ) * B_word := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ j * B_word := mul_le_mul_of_nonneg_right hcard hB_nn
  refine hjet_le.trans ?_
  have hc2_le : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc.le hcX 2
  have h1_le_X2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ h1X
  have hfactor : 1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta ≤
      (1 + (4 / (2 * Real.pi ^ 2)) * S_zeta) * X ^ 2 := by
    have h1 : (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta =
        (4 / (2 * Real.pi ^ 2)) * S_zeta * c ^ 2 := by ring
    rw [h1]
    have h2 : (4 / (2 * Real.pi ^ 2)) * S_zeta * c ^ 2 ≤
        (4 / (2 * Real.pi ^ 2)) * S_zeta * X ^ 2 :=
      mul_le_mul_of_nonneg_left hc2_le (by positivity)
    nlinarith
  have habs := polyPS_mul_polyP_exp_le N_V N_F hC_V hC_F hlam_F hν hc1 hs.le
  let E_out : ℝ := Real.exp (-(lam_out * ν * s / c ^ 2))
  calc (2 : ℝ) ^ j * B_word
      = (2 : ℝ) ^ (ℓ + 1 + 2 * j) * (M_V * M_F) *
          (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta) := by
        dsimp [B_word]
        rw [show ℓ + 1 + 2 * j = j + (ℓ + 1 + j) by omega, pow_add]
        ring
    _ ≤ (2 : ℝ) ^ (ℓ + 1 + 2 * j) *
          (polyP (C_V * C_F * K_abs) (4 * N_V + N_F) ν c * E_out) *
          ((1 + (4 / (2 * Real.pi ^ 2)) * S_zeta) * X ^ 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left habs (by positivity))
          hfactor
          (by positivity)
          (by unfold polyP; dsimp [E_out]; positivity)
    _ = polyP C_out N_out ν c * E_out := by
        dsimp [C_out, N_out, X]
        unfold polyP
        rw [pow_add]
        ring

end UnforcedLeray.Short.PartI

end
