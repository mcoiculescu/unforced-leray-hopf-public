import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.T20_1_Aux
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.OscMeanLap
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanDerivS
import UnforcedLeray.Units.B0151.DivCurl

/-!
# `PartI:T20/1/1` (`Sub/PartI_T20_1/PressureStep.lean`): All-Age-Order Cylinder Pressure Jet Step

Source of record: `the November 2 reference manuscript`, lines 517–526
(and 483–516, 276–288).

This module proves `trainPressureAgeJetSupStep_proof : TrainPressureAgeJetSupStep`:
given `hOv : TrainOverlap`, `hVort : ∀ r ≤ ℓ, TrainVorticityGaussianTailAt r`, and
`hVel : ∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r`, for every `ρ > 1/2` and spatial order `k : ℕ`,
there exist `C_p > 0`, `N_p : ℕ`, and `ν₀ > 0` such that for all `0 < ν ≤ ν₀`, every `BUC` train
`tr : B0140.TrainSol ν (trainPeriod ρ ν)`, `s > 0`, and `z : Plane`,
`‖ageJet ℓ k tr.p s z‖ ≤ polyP C_p N_p ν (trainPeriod ρ ν)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI.VelAgeJetAux
open UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet lapS vecLaplacian gradS
  advection momentumResidual)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm)

namespace PartI_T20_1

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

theorem derivWord_sub {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List Bool) (z : Plane) :
    B0151.derivWord w (fun x => f x - g x) z =
      B0151.derivWord w f z - B0151.derivWord w g z := by
  have hsub : (fun x => f x - g x) = fun x => f x + (-g x) := funext fun x => sub_eq_add_neg _ _
  rw [hsub, derivWord_add hf hg.neg w z, derivWord_neg g w z, ← sub_eq_add_neg]

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

theorem smR_derivWord {F : ℝ → Plane → ℝ}
    (hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2)) :
    ∀ w : List Bool, PartI_T20.SmR (fun x : ℝ × Plane => B0151.derivWord w (F x.1) x.2)
  | [] => hF
  | true :: w =>
    PartI_T20.smR_partialQ (F := fun r z => B0151.derivWord w (F r) z) (smR_derivWord hF w)
  | false :: w =>
    PartI_T20.smR_partialEta (F := fun r z => B0151.derivWord w (F r) z) (smR_derivWord hF w)

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

theorem iteratedDeriv_derivWord_eq {F : ℝ → Plane → ℝ}
    (hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2)) :
    ∀ (w : List Bool) (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ z : Plane,
      iteratedDeriv ℓ (fun r => B0151.derivWord w (F r) z) t =
        B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => F r z') t) z
  | [], _, _, _, _ => rfl
  | true :: w, ℓ, t, ht, z => by
    change iteratedDeriv ℓ (fun r => Cyl.partialQ (B0151.derivWord w (F r)) z) t =
      Cyl.partialQ (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => F r z') t)) z
    rw [PartI_T20.iteratedDeriv_partialQ_eq (F := fun r x => B0151.derivWord w (F r) x)
      (smR_derivWord hF w) ℓ ht z]
    congr 1
    funext x
    exact iteratedDeriv_derivWord_eq hF w ℓ ht x
  | false :: w, ℓ, t, ht, z => by
    change iteratedDeriv ℓ (fun r => Cyl.partialEta (B0151.derivWord w (F r)) z) t =
      Cyl.partialEta (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => F r z') t)) z
    rw [PartI_T20.iteratedDeriv_partialEta_eq (F := fun r x => B0151.derivWord w (F r) x)
      (smR_derivWord hF w) ℓ ht z]
    congr 1
    funext x
    exact iteratedDeriv_derivWord_eq hF w ℓ ht x

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

/-! ### 2. Horizontal mean identity and bound for `B0151.derivWord w (P_ℓ s)` -/

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

theorem iteratedDeriv_hmean_eq {c : ℝ} (hc : 0 < c) {F : ℝ → Plane → ℝ}
    (hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2)) :
    ∀ (ℓ : ℕ) {s : ℝ}, 0 < s → ∀ η : ℝ,
      iteratedDeriv ℓ (fun r => hmean c (F r) η) s =
        hmean c (fun z => iteratedDeriv ℓ (fun r => F r z) s) η
  | 0, _, _, _ => rfl
  | ℓ + 1, s, hs, η => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => hmean c (F r) η) =ᶠ[𝓝 s]
        fun r => hmean c (fun z => iteratedDeriv ℓ (fun r' => F r' z) r) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using iteratedDeriv_hmean_eq hc hF ℓ hr η
    rw [hev.deriv_eq, hmeanDerivS c hc (fun r z => iteratedDeriv ℓ (fun r' => F r' z) r)
      (smR_iteratedDeriv hF ℓ) s hs η]
    simp only [iteratedDeriv_succ]

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
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
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

theorem abs_hmean_derivWord_p_le {ν c M_V : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ k : ℕ) {w : List Bool} (hw : w.length = k) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hV_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k, ‖ageJet r i tr.v s w'‖ ≤ M_V) :
    |hmean c (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z.2| ≤
      (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
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
    have hpv := congrArg (fun v : Vec => v 1 ^ 2) (tr.isTrain.periodic_v r hr.le z')
    exact hpv
  have hmean_eq : ∀ η : ℝ, hmean c P_ℓ η = -hmean c G_ℓ η := by
    intro η
    rw [← iteratedDeriv_hmean_eq hc hsm_p ℓ hs η,
      ← iteratedDeriv_hmean_eq hc (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs η,
      ← iteratedDeriv_neg]
    have hev : (fun r => hmean c (tr.p r) η) =ᶠ[𝓝 s]
        fun r => -hmean c (fun z' : Plane => tr.v r z' 1 ^ 2) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using train_hmean_p_eq_neg_v1_sq hν hc1 tr htr hr η
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
    _ ≤ (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
        refine PartI_T20.norm_ageJet_mul_le
          (A := fun r z' => tr.v r z' 1) (B := fun r z' => tr.v r z' 1)
          hsm_v1 hsm_v1 ℓ k hs hMV hMV w' (fun r hr i hi => ?_) (fun r hr i hi => ?_)
        · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs w').trans (hV_bd w' r hr i hi)
        · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs w').trans (hV_bd w' r hr i hi)

/-! ### 3. Oscillating part bound via time-averaged momentum equation and `PbOscLinear` -/

/-- Explicit quantitative form of `pbOscLinear_of` (`Sub/T02_2_3/OscLinear.lean`). -/
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

theorem abs_lapS_derivWord_p_le {ν c M_V : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {t : ℝ} (ht : 0 < t) (z : Plane)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v t z‖ ≤ M_V) :
    |Train.lapS (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') t)) z| ≤
      4 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_src : PartI_T20.SmR (fun x : ℝ × Plane => poissonSource (tr.v x.1) x.2) :=
    smR_poissonSource hsm_v
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') t
  have hP_sm : ContDiff ℝ ∞ P_ℓ := contDiff_iteratedDeriv_slice hsm_p ℓ ht
  have hlap_P : Train.lapS P_ℓ =
      fun z' => -iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') t := by
    funext z'
    have h1 := PartI_T20.iteratedDeriv_mul_lapS_eq hsm_p 1 ℓ ht z'
    simp only [one_mul] at h1
    rw [← h1, ← iteratedDeriv_neg]
    have hev : (fun r => Train.lapS (tr.p r) z') =ᶠ[𝓝 t]
        fun r => -poissonSource (tr.v r) z' := by
      filter_upwards [Ioi_mem_nhds ht] with r (hr : 0 < r)
      exact slicePoisson ν c (r + 1) tr.v tr.p hν hc1 (by linarith)
        (trainSol_isClassicalOn tr (r + 1)) r ⟨hr.le, by linarith⟩ z'
    exact hev.iteratedDeriv_eq ℓ
  rw [derivWord_lapS_comm hP_sm w z, hlap_P, derivWord_neg _ w z, abs_neg]
  calc |B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') t) z|
      ≤ ‖ageJet ℓ k (fun r z' => poissonSource (tr.v r) z') t z‖ :=
        abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => poissonSource (tr.v r) z')
          hsm_src ℓ k hw ht z
    _ ≤ 4 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V :=
        norm_ageJet_poissonSource_le hsm_v ℓ k ht hMV z hV_bd

/-- Spatial viscous-minus-advection part of component `m` of the momentum equation:
`ν Δv_m - v_0 ∂_q v_m - v_1 ∂_η v_m`. -/
def viscAdv (ν : ℝ) (v : ℝ → Plane → Vec) (m : Fin 2) (r : ℝ) (z : Plane) : ℝ :=
  ν * Train.lapS (fun y => v r y m) z
  - v r z 0 * Cyl.partialQ (fun y => v r y m) z
  - v r z 1 * Cyl.partialEta (fun y => v r y m) z

theorem smR_viscAdv {ν : ℝ} {v : ℝ → Plane → Vec}
    (hv : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => v x.1 x.2)) (m : Fin 2) :
    PartI_T20.SmR (fun x : ℝ × Plane => viscAdv ν v m x.1 x.2) := by
  have hvm : PartI_T20.SmR (fun x : ℝ × Plane => v x.1 x.2 m) :=
    (EuclideanSpace.proj m : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  have hv0 : PartI_T20.SmR (fun x : ℝ × Plane => v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  have hv1 : PartI_T20.SmR (fun x : ℝ × Plane => v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  have h1 : PartI_T20.SmR (fun x : ℝ × Plane => ν * Train.lapS (fun y => v x.1 y m) x.2) :=
    PartI_T20.smR_mul_lapS (F := fun r y => v r y m) hvm ν
  have h2 : PartI_T20.SmR (fun x : ℝ × Plane => v x.1 x.2 0 * Cyl.partialQ (fun y => v x.1 y m) x.2) :=
    hv0.mul (PartI_T20.smR_partialQ (F := fun r y => v r y m) hvm)
  have h3 : PartI_T20.SmR (fun x : ℝ × Plane => v x.1 x.2 1 * Cyl.partialEta (fun y => v x.1 y m) x.2) :=
    hv1.mul (PartI_T20.smR_partialEta (F := fun r y => v r y m) hvm)
  exact (h1.sub h2).sub h3

theorem norm_ageJet_viscAdv_le {ν c M_V : ℝ} (hν : 0 ≤ ν) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (m : Fin 2) (ℓ k : ℕ) {t : ℝ} (ht : 0 < t) (z : Plane)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 2, ‖ageJet r i tr.v t z‖ ≤ M_V) :
    ‖ageJet ℓ k (viscAdv ν tr.v m) t z‖ ≤
      (2 * ν) * M_V + 2 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hvm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 m) :=
    (EuclideanSpace.proj m : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hv0 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hv1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  let F₁ : ℝ → Plane → ℝ := fun r w => ν * Train.lapS (fun y => tr.v r y m) w
  let F₂ : ℝ → Plane → ℝ := fun r w => tr.v r w 0 * Cyl.partialQ (fun y => tr.v r y m) w
  let F₃ : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * Cyl.partialEta (fun y => tr.v r y m) w
  have hsm₁ : PartI_T20.SmR (fun x : ℝ × Plane => F₁ x.1 x.2) :=
    PartI_T20.smR_mul_lapS (F := fun r y => tr.v r y m) hvm ν
  have hsm₂ : PartI_T20.SmR (fun x : ℝ × Plane => F₂ x.1 x.2) :=
    hv0.mul (PartI_T20.smR_partialQ (F := fun r y => tr.v r y m) hvm)
  have hsm₃ : PartI_T20.SmR (fun x : ℝ × Plane => F₃ x.1 x.2) :=
    hv1.mul (PartI_T20.smR_partialEta (F := fun r y => tr.v r y m) hvm)
  have hsub2 := PartI_T20.ageJet_sub (fun r w => F₁ r w - F₂ r w) F₃ (hsm₁.sub hsm₂) hsm₃ ht ℓ k z
  have hsub1 := PartI_T20.ageJet_sub F₁ F₂ hsm₁ hsm₂ ht ℓ k z
  have hsplit : ageJet ℓ k (viscAdv ν tr.v m) t z =
      ageJet ℓ k F₁ t z - ageJet ℓ k F₂ t z - ageJet ℓ k F₃ t z := by
    change ageJet ℓ k (fun r w => F₁ r w - F₂ r w - F₃ r w) t z = _
    rw [hsub2, hsub1]
  have hb₁ : ‖ageJet ℓ k F₁ t z‖ ≤ (2 * ν) * M_V := by
    calc ‖ageJet ℓ k F₁ t z‖
        ≤ (2 * ν) * ‖ageJet ℓ (k + 2) (fun r w => tr.v r w m) t z‖ :=
          PartI_T20.norm_ageJet_mul_lapS_le (F := fun r w => tr.v r w m) hvm hν ℓ k ht z
      _ ≤ (2 * ν) * ‖ageJet ℓ (k + 2) tr.v t z‖ :=
          mul_le_mul_of_nonneg_left (PartI_T20.norm_ageJet_vec_proj_le hsm_v m ℓ (k + 2) ht z) (by positivity)
      _ ≤ (2 * ν) * M_V :=
          mul_le_mul_of_nonneg_left (hV_bd ℓ le_rfl (k + 2) le_rfl) (by positivity)
  have hb₂ : ‖ageJet ℓ k F₂ t z‖ ≤ (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
    refine PartI_T20.norm_ageJet_mul_le
      (A := fun r w => tr.v r w 0) (B := fun r w => Cyl.partialQ (fun y => tr.v r y m) w)
      hv0 (PartI_T20.smR_partialQ (F := fun r w => tr.v r w m) hvm)
      ℓ k ht hMV hMV z (fun r hr i hi => ?_) (fun r hr i hi => ?_)
    · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 0 r i ht z).trans (hV_bd r hr i (by omega))
    · exact (PartI_T20.norm_ageJet_partialQ_le (F := fun r w => tr.v r w m) hvm r i ht z).trans
        ((PartI_T20.norm_ageJet_vec_proj_le hsm_v m r (i + 1) ht z).trans
          (hV_bd r hr (i + 1) (by omega)))
  have hb₃ : ‖ageJet ℓ k F₃ t z‖ ≤ (2 : ℝ) ^ (ℓ + k) * M_V * M_V := by
    refine PartI_T20.norm_ageJet_mul_le
      (A := fun r w => tr.v r w 1) (B := fun r w => Cyl.partialEta (fun y => tr.v r y m) w)
      hv1 (PartI_T20.smR_partialEta (F := fun r w => tr.v r w m) hvm)
      ℓ k ht hMV hMV z (fun r hr i hi => ?_) (fun r hr i hi => ?_)
    · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i ht z).trans (hV_bd r hr i (by omega))
    · exact (PartI_T20.norm_ageJet_partialEta_le (F := fun r w => tr.v r w m) hvm r i ht z).trans
        ((PartI_T20.norm_ageJet_vec_proj_le hsm_v m r (i + 1) ht z).trans
          (hV_bd r hr (i + 1) (by omega)))
  rw [hsplit]
  have hn1 := norm_sub_le (ageJet ℓ k F₁ t z - ageJet ℓ k F₂ t z) (ageJet ℓ k F₃ t z)
  have hn2 := norm_sub_le (ageJet ℓ k F₁ t z) (ageJet ℓ k F₂ t z)
  linarith

theorem partialQ_train_p_eq_viscAdv_sub_DtR {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialQ (tr.p t) w =
      viscAdv ν tr.v 0 t w - PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (t, w) := by
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have m := congrArg (fun X : Vec => X 0) (tr.isTrain.momentum t ht w)
  simp only [momentumResidual, advection, vecLaplacian, gradS,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    toVec_zero, PiLp.zero_apply] at m
  have hd1 := PartI_T20.iteratedDeriv_vec_proj_eq hsm_v 0 1 ht w
  rw [iteratedDeriv_one, iteratedDeriv_one] at hd1
  have hd2 := PartI_T20.iteratedDeriv_slice_eq_DtR (F := fun y : ℝ × Plane => tr.v y.1 y.2 0)
    hsm_v0 1 ht w
  rw [iteratedDeriv_one] at hd2
  unfold viscAdv
  linarith

theorem partialEta_train_p_eq_viscAdv_sub_DtR {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialEta (tr.p t) w =
      viscAdv ν tr.v 1 t w - PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (t, w) := by
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have m := congrArg (fun X : Vec => X 1) (tr.isTrain.momentum t ht w)
  simp only [momentumResidual, advection, vecLaplacian, gradS,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    toVec_one, PiLp.zero_apply] at m
  have hd1 := PartI_T20.iteratedDeriv_vec_proj_eq hsm_v 1 1 ht w
  rw [iteratedDeriv_one, iteratedDeriv_one] at hd1
  have hd2 := PartI_T20.iteratedDeriv_slice_eq_DtR (F := fun y : ℝ × Plane => tr.v y.1 y.2 1)
    hsm_v1 1 ht w
  rw [iteratedDeriv_one] at hd2
  unfold viscAdv
  linarith

theorem partialQ_derivWord_p_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (w : List Bool) {t : ℝ} (ht : 0 < t) (z : Plane) :
    Cyl.partialQ (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') t)) z =
      B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 0 r z') t) z -
        deriv (fun τ => iteratedDeriv ℓ
          (fun r => B0151.derivWord w (fun z' => tr.v r z' 0) z) τ) t := by
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_va : PartI_T20.SmR (fun x : ℝ × Plane => viscAdv ν tr.v 0 x.1 x.2) :=
    smR_viscAdv hsm_v 0
  have hsm_dt : PartI_T20.SmR
      (fun x : ℝ × Plane => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) x) :=
    PartI_T20.smR_DtR hsm_v0 1
  have hP_sm : ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ (fun r => tr.p r z') t) :=
    contDiff_iteratedDeriv_slice hsm_p ℓ ht
  have hVA_sm : ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 0 r z') t) :=
    contDiff_iteratedDeriv_slice hsm_va ℓ ht
  have hDT_sm : ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ
      (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (r, z')) t) :=
    contDiff_iteratedDeriv_slice
      (F := fun r z' => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (r, z')) hsm_dt ℓ ht
  have hslice_eq : Cyl.partialQ (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') t) =
      fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 0 r z') t -
        iteratedDeriv ℓ (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (r, z')) t := by
    funext z'
    rw [← PartI_T20.iteratedDeriv_partialQ_eq hsm_p ℓ ht z']
    have hev : (fun r => Cyl.partialQ (tr.p r) z') =ᶠ[𝓝 t]
        fun r => viscAdv ν tr.v 0 r z' -
          PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (r, z') := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using
        partialQ_train_p_eq_viscAdv_sub_DtR tr hr z'
    rw [hev.iteratedDeriv_eq ℓ]
    exact iteratedDeriv_sub
      (UnforcedLeray.Short.IIb.vb_slice_smooth_at (viscAdv ν tr.v 0) hsm_va ht z' ℓ)
      (UnforcedLeray.Short.IIb.vb_slice_smooth_at
        (fun r w => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (r, w)) hsm_dt ht z' ℓ)
  have hdt_eq : (fun z' => iteratedDeriv ℓ
      (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (r, z')) t) =
      fun z' => iteratedDeriv (ℓ + 1) (fun r => tr.v r z' 0) t := by
    funext z'
    rw [iteratedDeriv_succ']
    have hev : (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 0) (r, z')) =ᶠ[𝓝 t]
        deriv (fun r => tr.v r z' 0) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr
      rw [← PartI_T20.iteratedDeriv_slice_eq_DtR hsm_v0 1 hr z', iteratedDeriv_one]
    exact hev.iteratedDeriv_eq ℓ
  rw [derivWord_partialQ_comm hP_sm w, hslice_eq, derivWord_sub hVA_sm hDT_sm w z,
    hdt_eq, ← iteratedDeriv_derivWord_eq (F := fun r z' => tr.v r z' 0) hsm_v0 w (ℓ + 1) ht z,
    iteratedDeriv_succ]

theorem partialEta_derivWord_p_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (w : List Bool) {t : ℝ} (ht : 0 < t) (z : Plane) :
    Cyl.partialEta (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') t)) z =
      B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 1 r z') t) z -
        deriv (fun τ => iteratedDeriv ℓ
          (fun r => B0151.derivWord w (fun z' => tr.v r z' 1) z) τ) t := by
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_va : PartI_T20.SmR (fun x : ℝ × Plane => viscAdv ν tr.v 1 x.1 x.2) :=
    smR_viscAdv hsm_v 1
  have hsm_dt : PartI_T20.SmR
      (fun x : ℝ × Plane => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) x) :=
    PartI_T20.smR_DtR hsm_v1 1
  have hP_sm : ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ (fun r => tr.p r z') t) :=
    contDiff_iteratedDeriv_slice hsm_p ℓ ht
  have hVA_sm : ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 1 r z') t) :=
    contDiff_iteratedDeriv_slice hsm_va ℓ ht
  have hDT_sm : ContDiff ℝ ∞ (fun z' : Plane => iteratedDeriv ℓ
      (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (r, z')) t) :=
    contDiff_iteratedDeriv_slice
      (F := fun r z' => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (r, z')) hsm_dt ℓ ht
  have hslice_eq : Cyl.partialEta (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') t) =
      fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 1 r z') t -
        iteratedDeriv ℓ (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (r, z')) t := by
    funext z'
    rw [← PartI_T20.iteratedDeriv_partialEta_eq hsm_p ℓ ht z']
    have hev : (fun r => Cyl.partialEta (tr.p r) z') =ᶠ[𝓝 t]
        fun r => viscAdv ν tr.v 1 r z' -
          PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (r, z') := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using
        partialEta_train_p_eq_viscAdv_sub_DtR tr hr z'
    rw [hev.iteratedDeriv_eq ℓ]
    exact iteratedDeriv_sub
      (UnforcedLeray.Short.IIb.vb_slice_smooth_at (viscAdv ν tr.v 1) hsm_va ht z' ℓ)
      (UnforcedLeray.Short.IIb.vb_slice_smooth_at
        (fun r w => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (r, w)) hsm_dt ht z' ℓ)
  have hdt_eq : (fun z' => iteratedDeriv ℓ
      (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (r, z')) t) =
      fun z' => iteratedDeriv (ℓ + 1) (fun r => tr.v r z' 1) t := by
    funext z'
    rw [iteratedDeriv_succ']
    have hev : (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 1) (r, z')) =ᶠ[𝓝 t]
        deriv (fun r => tr.v r z' 1) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr
      rw [← PartI_T20.iteratedDeriv_slice_eq_DtR hsm_v1 1 hr z', iteratedDeriv_one]
    exact hev.iteratedDeriv_eq ℓ
  rw [derivWord_partialEta_comm hP_sm w, hslice_eq, derivWord_sub hVA_sm hDT_sm w z,
    hdt_eq, ← iteratedDeriv_derivWord_eq (F := fun r z' => tr.v r z' 1) hsm_v1 w (ℓ + 1) ht z,
    iteratedDeriv_succ]

theorem abs_timeIntegral_partial_le {ν c M_V s : ℝ} (hν : 0 < ν) (hMV : 0 ≤ M_V) (hs : 0 < s)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    (hV_bd : ∀ t : ℝ, 0 < t → ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 2, ‖ageJet r i tr.v t z'‖ ≤ M_V) :
    let Q_shift : ℝ → Plane → ℝ := fun σ z' =>
      B0151.derivWord w (fun y => iteratedDeriv ℓ (fun r => tr.p r y) (s / 2 + σ)) z'
    let G_va : ℝ := (2 * ν) * M_V + 2 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V
    let L : ℝ := s * G_va + 2 * M_V
    ∀ a ∈ Icc (0 : ℝ) s, ∀ b ∈ Icc (0 : ℝ) s, a ≤ b → ∀ z : Plane,
      |∫ σ in a..b, Cyl.partialQ (Q_shift σ) z| ≤ L ∧
      |∫ σ in a..b, Cyl.partialEta (Q_shift σ) z| ≤ L := by
  intro Q_shift G_va L a ha b hb hab z
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hGva_nn : 0 ≤ G_va := by dsimp [G_va]; positivity
  have hsub_ab : b - a ≤ s := by linarith [ha.1, hb.2]
  have hba_nn : 0 ≤ b - a := sub_nonneg.2 hab
  have hbound_m : ∀ m : Fin 2,
      let A_m : ℝ → ℝ := fun σ =>
        B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v m r z') (s / 2 + σ)) z
      let Φ_m : ℝ → ℝ := fun τ =>
        iteratedDeriv ℓ (fun r => B0151.derivWord w (fun z' => tr.v r z' m) z) τ
      |∫ σ in a..b, (A_m σ - deriv Φ_m (s / 2 + σ))| ≤ L := by
    intro m A_m Φ_m
    have hsm_vm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 m) :=
      (EuclideanSpace.proj m : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
    have hsm_va : PartI_T20.SmR (fun x : ℝ × Plane => viscAdv ν tr.v m x.1 x.2) :=
      smR_viscAdv hsm_v m
    have hsm_A : PartI_T20.SmR (fun x : ℝ × Plane =>
        B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v m r z') x.1) x.2) :=
      smR_derivWord (F := fun t z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v m r z') t)
        (smR_iteratedDeriv hsm_va ℓ) w
    have hsm_Φ : PartI_T20.SmR (fun x : ℝ × Plane =>
        iteratedDeriv ℓ (fun r => B0151.derivWord w (fun z' => tr.v r z' m) x.2) x.1) :=
      smR_iteratedDeriv (F := fun r z' => B0151.derivWord w (fun y => tr.v r y m) z')
        (smR_derivWord (F := fun r y => tr.v r y m) hsm_vm w) ℓ
    have hA_cont : ContinuousOn A_m (uIcc a b) := by
      rw [uIcc_of_le hab]
      have hmap : Continuous (fun σ : ℝ => ((s / 2 + σ, z) : ℝ × Plane)) :=
        (continuous_const.add continuous_id).prodMk continuous_const
      exact hsm_A.continuousOn.comp hmap.continuousOn
        (fun σ hσ => mem_UU (by linarith [ha.1, hσ.1]))
    have hΦ_diff : ∀ σ ∈ uIcc a b,
        HasDerivAt (fun τ => Φ_m (s / 2 + τ)) (deriv Φ_m (s / 2 + σ)) σ := by
      intro σ hσ
      rw [uIcc_of_le hab] at hσ
      have ht : 0 < s / 2 + σ := by linarith [ha.1, hσ.1]
      have h1 : ContDiffAt ℝ ∞ Φ_m (s / 2 + σ) := by
        have hpt : ContDiffAt ℝ ∞ (fun x : ℝ × Plane =>
            iteratedDeriv ℓ (fun r => B0151.derivWord w (fun z' => tr.v r z' m) x.2) x.1)
            (s / 2 + σ, z) := hsm_Φ.contDiffAt (isOpen_UU.mem_nhds (mem_UU ht))
        exact hpt.comp (s / 2 + σ) (contDiffAt_id.prodMk contDiffAt_const)
      have h2 : HasDerivAt Φ_m (deriv Φ_m (s / 2 + σ)) (s / 2 + σ) :=
        (h1.differentiableAt (by simp)).hasDerivAt
      have h3 : HasDerivAt (fun τ : ℝ => s / 2 + τ) 1 σ :=
        (hasDerivAt_id σ).const_add (s / 2)
      have hcomp : HasDerivAt (fun τ => Φ_m (s / 2 + τ)) (deriv Φ_m (s / 2 + σ) * 1) σ :=
        h2.comp σ h3
      rwa [mul_one] at hcomp
    have hΦ'_cont : ContinuousOn (fun σ => deriv Φ_m (s / 2 + σ)) (uIcc a b) := by
      rw [uIcc_of_le hab]
      have hsm_dΦ : PartI_T20.SmR (fun x : ℝ × Plane =>
          iteratedDeriv (ℓ + 1) (fun r => B0151.derivWord w (fun z' => tr.v r z' m) x.2) x.1) :=
        smR_iteratedDeriv (F := fun r z' => B0151.derivWord w (fun y => tr.v r y m) z')
          (smR_derivWord (F := fun r y => tr.v r y m) hsm_vm w) (ℓ + 1)
      have hmap : Continuous (fun σ : ℝ => ((s / 2 + σ, z) : ℝ × Plane)) :=
        (continuous_const.add continuous_id).prodMk continuous_const
      refine (hsm_dΦ.continuousOn.comp hmap.continuousOn
        (fun σ hσ => mem_UU (by linarith [ha.1, hσ.1]))).congr (fun σ _ => ?_)
      exact (congrFun iteratedDeriv_succ (s / 2 + σ)).symm
    have hint_A : IntervalIntegrable A_m volume a b := hA_cont.intervalIntegrable
    have hint_Φ' : IntervalIntegrable (fun σ => deriv Φ_m (s / 2 + σ)) volume a b :=
      hΦ'_cont.intervalIntegrable
    have hftc : ∫ σ in a..b, deriv Φ_m (s / 2 + σ) = Φ_m (s / 2 + b) - Φ_m (s / 2 + a) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ_diff hint_Φ'
    rw [intervalIntegral.integral_sub hint_A hint_Φ', hftc]
    have hA_bd : ∀ σ ∈ Ioc a b, ‖A_m σ‖ ≤ G_va := by
      intro σ hσ
      have ht : 0 < s / 2 + σ := by linarith [ha.1, hσ.1]
      rw [Real.norm_eq_abs]
      calc |A_m σ|
          ≤ ‖ageJet ℓ k (viscAdv ν tr.v m) (s / 2 + σ) z‖ :=
            abs_derivWord_iteratedDeriv_le_ageJet hsm_va ℓ k hw ht z
        _ ≤ G_va := norm_ageJet_viscAdv_le hν.le hMV tr m ℓ k ht z (hV_bd (s / 2 + σ) ht z)
    have hint_bd : |∫ σ in a..b, A_m σ| ≤ G_va * (b - a) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := A_m) (a := a) (b := b) (C := G_va) fun σ hσ => by
          rw [Set.uIoc_of_le hab] at hσ
          exact hA_bd σ hσ
      rwa [Real.norm_eq_abs, abs_of_nonneg hba_nn] at h
    have hΦ_bd : ∀ τ : ℝ, 0 < τ → |Φ_m τ| ≤ M_V := by
      intro τ hτ
      dsimp [Φ_m]
      rw [iteratedDeriv_derivWord_eq (F := fun r z' => tr.v r z' m) hsm_vm w ℓ hτ z]
      calc |B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.v r z' m) τ) z|
          ≤ ‖ageJet ℓ k (fun r z' => tr.v r z' m) τ z‖ :=
            abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => tr.v r z' m)
              hsm_vm ℓ k hw hτ z
        _ ≤ ‖ageJet ℓ k tr.v τ z‖ := PartI_T20.norm_ageJet_vec_proj_le hsm_v m ℓ k hτ z
        _ ≤ M_V := hV_bd τ hτ z ℓ le_rfl k (by omega)
    have hΦ_b : |Φ_m (s / 2 + b)| ≤ M_V := hΦ_bd (s / 2 + b) (by linarith [hb.1])
    have hΦ_a : |Φ_m (s / 2 + a)| ≤ M_V := hΦ_bd (s / 2 + a) (by linarith [ha.1])
    have htri1 := abs_sub (∫ σ in a..b, A_m σ) (Φ_m (s / 2 + b) - Φ_m (s / 2 + a))
    have htri2 := abs_sub (Φ_m (s / 2 + b)) (Φ_m (s / 2 + a))
    have hG_s : G_va * (b - a) ≤ s * G_va := by nlinarith
    dsimp [L]
    linarith
  refine ⟨?_, ?_⟩
  · have hcongr : ∫ σ in a..b, Cyl.partialQ (Q_shift σ) z =
        ∫ σ in a..b, (B0151.derivWord w
          (fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 0 r z') (s / 2 + σ)) z -
          deriv (fun τ => iteratedDeriv ℓ
            (fun r => B0151.derivWord w (fun z' => tr.v r z' 0) z) τ) (s / 2 + σ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [uIcc_of_le hab] at hσ
      exact partialQ_derivWord_p_eq tr ℓ w (by linarith [ha.1, hσ.1]) z
    rw [hcongr]
    exact hbound_m 0
  · have hcongr : ∫ σ in a..b, Cyl.partialEta (Q_shift σ) z =
        ∫ σ in a..b, (B0151.derivWord w
          (fun z' => iteratedDeriv ℓ (fun r => viscAdv ν tr.v 1 r z') (s / 2 + σ)) z -
          deriv (fun τ => iteratedDeriv ℓ
            (fun r => B0151.derivWord w (fun z' => tr.v r z' 1) z) τ) (s / 2 + σ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [uIcc_of_le hab] at hσ
      exact partialEta_derivWord_p_eq tr ℓ w (by linarith [ha.1, hσ.1]) z
    rw [hcongr]
    exact hbound_m 1

theorem abs_osc_derivWord_p_le {ν c M_V : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hV_bd : ∀ t : ℝ, 0 < t → ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 2, ‖ageJet r i tr.v t z'‖ ≤ M_V) :
    let Q_s : Plane → ℝ := B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)
    let K_src : ℝ := 4 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V
    |Q_s z - hmean c Q_s z.2| ≤
      (K_src * c ^ 2 / (2 * Real.pi ^ 2)) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  intro Q_s K_src
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hK_nn : 0 ≤ K_src := by dsimp [K_src]; positivity
  let M_osc : ℝ := (K_src * c ^ 2 / (2 * Real.pi ^ 2)) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  let Q : ℝ → Plane → ℝ := fun t z' =>
    B0151.derivWord w (fun y => iteratedDeriv ℓ (fun r => tr.p r y) t) z'
  let Q_shift : ℝ → Plane → ℝ := fun σ z' => Q (s / 2 + σ) z'
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_Q : PartI_T20.SmR (fun x : ℝ × Plane => Q x.1 x.2) :=
    smR_derivWord (F := fun t y => iteratedDeriv ℓ (fun r => tr.p r y) t)
      (smR_iteratedDeriv hsm_p ℓ) w
  have hsm_shift : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Q_shift x.1 x.2) (Icc 0 s ×ˢ univ) := by
    have hmap : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((s / 2 + x.1, x.2) : ℝ × Plane)) :=
      (contDiff_const.add contDiff_fst).prodMk contDiff_snd
    exact hsm_Q.comp hmap.contDiffOn (fun x hx => mem_UU (by linarith [hx.1.1]))
  have hper_shift : ∀ σ ∈ Icc (0 : ℝ) s, Cyl.IsPeriodic c (Q_shift σ) := by
    intro σ hσ
    have ht : 0 < s / 2 + σ := by linarith [hσ.1]
    exact isPeriodic_derivWord
      (isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ ht) w
  have hlap_shift : ∀ σ ∈ Icc (0 : ℝ) s, ∀ w' : Plane, |Train.lapS (Q_shift σ) w'| ≤ K_src := by
    intro σ hσ w'
    have ht : 0 < s / 2 + σ := by linarith [hσ.1]
    exact abs_lapS_derivWord_p_le hν hc1 hMV tr ℓ k hw ht w'
      (fun r hr i hi => hV_bd (s / 2 + σ) ht w' r hr i (by omega))
  have hL := abs_timeIntegral_partial_le hν hMV hs tr ℓ k hw hV_bd
  set L : ℝ := s * ((2 * ν) * M_V + 2 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V) + 2 * M_V
  have hAvg : ∀ a ∈ Icc (0 : ℝ) s, ∀ b ∈ Icc (0 : ℝ) s, a < b → ∀ w' : Plane,
      |pbAvg Q_shift a b w' - hmean c (pbAvg Q_shift a b) w'.2| ≤ M_osc := by
    intro a ha b hb hab w'
    obtain ⟨hP2, hPq, hPe, hPl⟩ := pbTimeAvgSmooth s Q_shift a b ha hb hsm_shift
    have hba : 0 < b - a := sub_pos.2 hab
    have hsub : uIcc a b ⊆ Icc 0 s := by
      rw [uIcc_of_le hab.le]
      exact Icc_subset_Icc ha.1 hb.2
    have hq_def : pbAvg Q_shift a b = fun y => (b - a)⁻¹ * ∫ σ in a..b, Q_shift σ y := rfl
    have hC2 : ContDiff ℝ 2 (pbAvg Q_shift a b) := by
      rw [hq_def]
      exact contDiff_const.mul hP2
    have hper : Cyl.IsPeriodic c (pbAvg Q_shift a b) := by
      intro y
      show (b - a)⁻¹ * ∫ σ in a..b, Q_shift σ (y.1 + c, y.2) =
        (b - a)⁻¹ * ∫ σ in a..b, Q_shift σ y
      congr 1
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      exact hper_shift σ (hsub hσ) y
    have hgrad : ∃ L' : ℝ, ∀ y, |Cyl.partialQ (pbAvg Q_shift a b) y| ≤ L' ∧
        |Cyl.partialEta (pbAvg Q_shift a b) y| ≤ L' := by
      refine ⟨(b - a)⁻¹ * L, fun y => ?_⟩
      obtain ⟨h1, h2⟩ := hL a ha b hb hab.le y
      rw [hq_def, pbc_partialQ_const_mul, pbc_partialEta_const_mul, hPq, hPe, abs_mul, abs_mul,
        abs_of_pos (inv_pos.2 hba)]
      exact ⟨mul_le_mul_of_nonneg_left h1 (inv_pos.2 hba).le,
        mul_le_mul_of_nonneg_left h2 (inv_pos.2 hba).le⟩
    have hlapq : ∀ y, |Train.lapS (pbAvg Q_shift a b) y| ≤ K_src := by
      intro y
      rw [hq_def, pbc_lapS_const_mul, hPl, abs_mul, abs_of_pos (inv_pos.2 hba)]
      have hint : |∫ σ in a..b, Train.lapS (Q_shift σ) y| ≤ K_src * |b - a| := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun σ => Train.lapS (Q_shift σ) y) (a := a) (b := b) (C := K_src)
          (fun σ hσ => by
            rw [Set.uIoc_of_le hab.le] at hσ
            rw [Real.norm_eq_abs]
            exact hlap_shift σ ⟨ha.1.trans hσ.1.le, hσ.2.trans hb.2⟩ y)
        simpa [Real.norm_eq_abs] using this
      calc (b - a)⁻¹ * |∫ σ in a..b, Train.lapS (Q_shift σ) y|
          ≤ (b - a)⁻¹ * (K_src * |b - a|) :=
            mul_le_mul_of_nonneg_left hint (inv_pos.2 hba).le
        _ = K_src := by
            rw [abs_of_pos hba]
            field_simp
    exact oscLinear_explicit hc hK_nn hC2 hper hgrad hlapq w'
  have hLim := pbAvgLimit_of pbHmeanTimeIntegral pbHmeanTimeContinuous pbRealAvgLimit
    c s M_osc Q_shift hc hs hsm_shift.continuousOn hAvg (s / 2) ⟨by linarith, by linarith⟩ z
  have hmid : Q_shift (s / 2) = Q_s := by
    funext w'
    dsimp [Q_shift, Q, Q_s]
    rw [add_halves]
  rwa [hmid] at hLim

end PartI_T20_1

/-! ### 4. Proof of `TrainPressureAgeJetSupStep` (`PartI:T20/1/1`) -/

/-- **All-age-order cylinder pressure jet step (`trainPressureAgeJetSupStep_proof`)**:
given `hOv : TrainOverlap`, `hVort : ∀ r ≤ ℓ, TrainVorticityGaussianTailAt r`, and
`hVel : ∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r`, bounds `‖ageJet ℓ k tr.p s z‖` by
`polyP C_p N_p ν (trainPeriod ρ ν)` uniformly in `s > 0` and `z : Plane`. -/
theorem trainPressureAgeJetSupStep_proof : TrainPressureAgeJetSupStep := by
  intro _hOv ℓ _hVort hVel ρ hρ k
  obtain ⟨C_V, N_V, ν_V, hCV, hνV, hV_rect⟩ :=
    PartI_T20.uniform_velocity_sup_rect hρ (k + 2) ℓ hVel
  let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun _ => by positivity
  let C_p : ℝ :=
    (2 : ℝ) ^ (ℓ + 2 * k) * C_V ^ 2 * (1 + (4 / (2 * Real.pi ^ 2)) * S_zeta)
  let N_p : ℕ := 2 * N_V + 2
  let ν₀ : ℝ := min ν_V 1
  have hCp : 0 < C_p := by dsimp [C_p]; positivity
  have hν₀ : 0 < ν₀ := lt_min hνV zero_lt_one
  refine ⟨C_p, N_p, ν₀, hCp, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs z
  have hν_V : ν ≤ ν_V := hν_le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc1 : 1 ≤ c := by
    unfold c trainPeriod
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  let X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ X := by dsimp [X]; linarith
  have hcX : c ≤ X := by dsimp [X]; linarith
  let M_V : ℝ := polyP C_V N_V ν c
  have hMV : 0 ≤ M_V := by dsimp [M_V, polyP]; positivity
  have hV_bd : ∀ t : ℝ, 0 < t → ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 2,
      ‖ageJet r i tr.v t z'‖ ≤ M_V :=
    fun t ht z' r hr i hi => hV_rect ν hν hν_V tr htr t ht z' r hr i hi
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ :=
    PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  let B_word : ℝ :=
    (2 : ℝ) ^ (ℓ + k) * M_V * M_V * (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta)
  have hword_bd : ∀ w ∈ wordsOfLength k, |B0151.derivWord w P_ℓ z| ≤ B_word := by
    intro w hw
    have hlen : w.length = k := by
      unfold wordsOfLength at hw
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hw
      simp
    have hmean_bd := PartI_T20_1.abs_hmean_derivWord_p_le hν hc1 hMV tr htr ℓ k hlen hs z
      (fun w' r hr i hi => hV_bd s hs w' r hr i (by omega))
    have hosc_bd := PartI_T20_1.abs_osc_derivWord_p_le hν hc1 hMV tr ℓ k hlen hs z hV_bd
    have htri : |B0151.derivWord w P_ℓ z| ≤
        |B0151.derivWord w P_ℓ z - hmean c (B0151.derivWord w P_ℓ) z.2| +
          |hmean c (B0151.derivWord w P_ℓ) z.2| := by
      have := abs_add_le (B0151.derivWord w P_ℓ z - hmean c (B0151.derivWord w P_ℓ) z.2)
        (hmean c (B0151.derivWord w P_ℓ) z.2)
      rwa [sub_add_cancel] at this
    calc |B0151.derivWord w P_ℓ z|
        ≤ (4 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta +
            (2 : ℝ) ^ (ℓ + k) * M_V * M_V :=
          htri.trans (add_le_add hosc_bd hmean_bd)
      _ = B_word := by dsimp [B_word]; ring
  have hjet_word := (cylJetWord_proof P_ℓ hP_sm k z).2
  have hcard_nat : (wordsOfLength k).card ≤ 2 ^ k := by
    unfold wordsOfLength
    exact Finset.card_image_le.trans (by simp)
  have hcard : ((wordsOfLength k).card : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hcard_nat
  have hB_nn : 0 ≤ B_word := by dsimp [B_word]; positivity
  have hjet_le : ‖ageJet ℓ k tr.p s z‖ ≤ (2 : ℝ) ^ k * B_word := by
    change ‖iteratedFDeriv ℝ k P_ℓ z‖ ≤ _
    calc ‖iteratedFDeriv ℝ k P_ℓ z‖
        ≤ ∑ w ∈ wordsOfLength k, |B0151.derivWord w P_ℓ z| := hjet_word
      _ ≤ ∑ _w ∈ wordsOfLength k, B_word := Finset.sum_le_sum fun w hw => hword_bd w hw
      _ = ((wordsOfLength k).card : ℝ) * B_word := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ k * B_word := mul_le_mul_of_nonneg_right hcard hB_nn
  refine hjet_le.trans ?_
  have hc2_le : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0 hcX 2
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
  calc (2 : ℝ) ^ k * B_word
      = (2 : ℝ) ^ (ℓ + 2 * k) * (M_V * M_V) *
          (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta) := by
        dsimp [B_word]
        rw [show ℓ + 2 * k = k + (ℓ + k) by omega, pow_add]
        ring
    _ ≤ (2 : ℝ) ^ (ℓ + 2 * k) * (M_V * M_V) *
          ((1 + (4 / (2 * Real.pi ^ 2)) * S_zeta) * X ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = polyP C_p N_p ν c := by
        dsimp [M_V, C_p, N_p, X]
        unfold polyP
        rw [show 2 * N_V + 2 = N_V + N_V + 2 by omega, pow_add, pow_add]
        ring

end UnforcedLeray.Short.PartI.VelAgeJetAux

end
