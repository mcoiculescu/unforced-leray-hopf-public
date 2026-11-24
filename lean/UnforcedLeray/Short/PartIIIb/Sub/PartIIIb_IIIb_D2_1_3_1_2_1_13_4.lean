import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L1
import UnforcedLeray.Lib.PhaseSpace.CutoffCalc

/-!
# `truncCommutator`: infrastructure and reduction to two weak-curl lemmas

Source `the November 2 reference manuscript`
lines 1334-1337, 1351-1362, 1470-1480.  Pointwise
`χ wOpT Z - wOpT(χ Z) = (½ y·∇χ + νΔχ) Z + 2ν ∑ₖ ∂ₖχ ∂ₖ Z` (`Z = curl Ψ`), weak integration by
parts with `spΦ.grad`, and the weak curl move for a general compactly supported smooth
multiplier `f` (`CurlMulGen`) applied to `(ψ, Φ)` and to `(∂ₖψ, ∂ₖΦ)` (`CurlOfGrad`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- A smooth scalar function of `y` vanishing outside a ball. -/
def SmF (f : Space → ℝ) : Prop := ContDiff ℝ ∞ f ∧ ∃ R : ℝ, ∀ y : Space, R < ‖y‖ → f y = 0

theorem sd_far {f : Space → ℝ} {R : ℝ} (hf : ∀ y : Space, R < ‖y‖ → f y = 0) (k : Fin 3)
    {y : Space} (hy : R < ‖y‖) : sd k f y = 0 := by
  have hopen : IsOpen {z : Space | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hev : f =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) fun z hz => hf z hz
  simp [sd, hev.fderiv_eq]

theorem SmF.sd {f : Space → ℝ} (h : SmF f) (k : Fin 3) : SmF (sd k f) := by
  obtain ⟨hc, R, hR⟩ := h
  exact ⟨contDiff_sd hc k, R, fun y hy => sd_far hR k hy⟩

theorem SmF.cut (n : ℕ) : SmF (cutχ n) :=
  ⟨contDiff_cutχ n, 2 * ((n : ℝ) + 1), fun y hy => cutχ_eq_zero n hy.le⟩

theorem SmF.radS {f : Space → ℝ} (h : SmF f) : SmF (radS f) := by
  obtain ⟨hc, R, hR⟩ := h
  refine ⟨?_, R, fun y hy => ?_⟩
  · unfold UnforcedLeray.PhaseSpace.radS
    apply ContDiff.sum
    intro j _
    exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).mul (contDiff_sd hc j)
  · simp [UnforcedLeray.PhaseSpace.radS, sd_far hR _ hy]

theorem SmF.lapS {f : Space → ℝ} (h : SmF f) : SmF (lapS f) := by
  obtain ⟨hc, R, hR⟩ := h
  refine ⟨?_, R, fun y hy => ?_⟩
  · unfold UnforcedLeray.PhaseSpace.lapS
    apply ContDiff.sum
    intro j _
    exact contDiff_sd (contDiff_sd hc j) j
  · have : ∀ j : Fin 3, UnforcedLeray.PhaseSpace.sd j (UnforcedLeray.PhaseSpace.sd j f) y = 0 :=
      fun j => _root_.UnforcedLeray.Short.PartIIIb.Concrete.sd_far
        (fun z hz => _root_.UnforcedLeray.Short.PartIIIb.Concrete.sd_far hR j hz) j hy
    simp [UnforcedLeray.PhaseSpace.lapS, this]

theorem SmF.const_mul {f : Space → ℝ} (h : SmF f) (c : ℝ) : SmF (fun y => c * f y) := by
  obtain ⟨hc, R, hR⟩ := h
  exact ⟨contDiff_const.mul hc, R, fun y hy => by simp [hR y hy]⟩

theorem SmF.add {f g : Space → ℝ} (hf : SmF f) (hg : SmF g) : SmF (fun y => f y + g y) := by
  obtain ⟨hc, R, hR⟩ := hf
  obtain ⟨hc', R', hR'⟩ := hg
  refine ⟨hc.add hc', max R R', fun y hy => ?_⟩
  simp [hR y (lt_of_le_of_lt (le_max_left _ _) hy), hR' y (lt_of_le_of_lt (le_max_right _ _) hy)]

theorem isPhaseTest_smulF {P : ℝ} {f : Space → ℝ} (hf : SmF f) {Θ : ℝ × Space → CVec3}
    (hΘ : IsPhaseTest P Θ) : IsPhaseTest P (fun x => f x.2 • Θ x) := by
  obtain ⟨hc, R, hR⟩ := hf
  refine ⟨(hc.comp contDiff_snd).smul hΘ.smooth, ?_, ?_⟩
  · intro τ y
    simp [hΘ.periodic τ y]
  · exact ⟨R, fun τ y hy => by simp [hR y hy]⟩

theorem isPhaseTest_crossGrad {P : ℝ} {f : Space → ℝ} (hf : SmF f) {Θ : ℝ × Space → CVec3}
    (hΘ : IsPhaseTest P Θ) : IsPhaseTest P (fun x => crossC (gradC f x.2) (Θ x)) := by
  have e : (fun x : ℝ × Space => crossC (gradC f x.2) (Θ x)) =
      ∑ j : Fin 3, fun x => sd j f x.2 • crossCR (EuclideanSpace.single j (1 : ℂ)) (Θ x) := by
    funext x
    rw [crossC_gradC_sum']
    simp [Finset.sum_apply, crossCR_apply]
  rw [e]
  exact IsPhaseTest.sum _ fun j _ =>
    isPhaseTest_smulF (hf.sd j) (hΘ.clm_comp (crossCR (EuclideanSpace.single j (1 : ℂ))))

theorem intPT {P : ℝ} (hP : 0 < P) {G w : ℝ × Space → CVec3} (hG : IsPhaseTest P G)
    (hw : LocL2 P w) :
    Integrable (fun x => dotL (G x) (w x)) (volume.restrict (phaseCell P)) :=
  wcm_integrable_dotL hP hG.continuous hG.bounded_support hw

theorem pairL_add_pt {P : ℝ} (hP : 0 < P) {F G w : ℝ × Space → CVec3}
    (hF : IsPhaseTest P F) (hG : IsPhaseTest P G) (hw : LocL2 P w) :
    pairF P (fun x => F x + G x) w = pairF P F w + pairF P G w := by
  have : Fact (0 < P) := ⟨hP⟩
  exact UnforcedLeray.Cons.C03.Concrete.pairF_add_left_of_integrable (intPT hP hF hw)
    (intPT hP hG hw) (intPT hP (hF.add hG : IsPhaseTest P (fun x => F x + G x)) hw)

theorem pairR_add {P : ℝ} (hP : 0 < P) {Ψ X Y : ℝ × Space → CVec3}
    (hX : Integrable (fun x => dotL (Ψ x) (X x)) (volume.restrict (phaseCell P)))
    (hY : Integrable (fun x => dotL (Ψ x) (Y x)) (volume.restrict (phaseCell P))) :
    pairF P Ψ (fun x => X x + Y x) = pairF P Ψ X + pairF P Ψ Y := by
  have : Fact (0 < P) := ⟨hP⟩
  refine UnforcedLeray.Cons.C03.Concrete.pairF_add_right_of_integrable hX hY ?_
  refine (hX.add hY).congr (ae_of_all _ fun x => ?_)
  simp [dotL_apply, Finset.sum_add_distrib, mul_add]

theorem pairF_neg_right (P : ℝ) (F G : ℝ × Space → CVec3) :
    pairF P F (fun x => -G x) = -pairF P F G := by
  simp only [pairF]
  rw [← phaseInt_neg']
  congr 1
  funext x
  simp [dotL_apply]

theorem pairF_neg_left (P : ℝ) (F G : ℝ × Space → CVec3) :
    pairF P (fun x => -F x) G = -pairF P F G := by
  simp only [pairF]
  rw [← phaseInt_neg']
  congr 1
  funext x
  simp [dotL_apply]

/-- The `Φ'`-and-`ψ'` combination `f Φ' + ∇f × ψ'` (`= curl (f ψ')` when `curl ψ' = Φ'`). -/
def Vf (f : Space → ℝ) (ψ' Φ' : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => f x.2 • Φ' x + crossC (gradC f x.2) (ψ' x)

theorem intV {P : ℝ} (hP : 0 < P) {f : Space → ℝ} (hf : SmF f) {Ψ ψ' Φ' : ℝ × Space → CVec3}
    (hΨ : IsPhaseTest P Ψ) (hψ : LocL2 P ψ') (hΦ : LocL2 P Φ') :
    Integrable (fun x => dotL (Ψ x) (Vf f ψ' Φ' x)) (volume.restrict (phaseCell P)) := by
  have h1 := intPT hP (isPhaseTest_smulF hf hΨ) hΦ
  have h2 := intPT hP (isPhaseTest_crossGrad hf hΨ) hψ
  refine (h1.add h2.neg).congr (ae_of_all _ fun x => ?_)
  have hadd : ∀ a b c : CVec3, dotL a (b + c) = dotL a b + dotL a c := fun a b c => by
    simp [dotL_apply, Finset.sum_add_distrib, mul_add]
  show dotL (f x.2 • Ψ x) (Φ' x) + -dotL (crossC (gradC f x.2) (Ψ x)) (ψ' x) =
    dotL (Ψ x) (f x.2 • Φ' x + crossC (gradC f x.2) (ψ' x))
  rw [hadd, ← dotL_real_smul', triple_dotL']

/-- (K1) Weak curl move for a general smooth compactly supported multiplier `f`:
`⟪f curl Ψ, ψ'⟫ = ⟪Ψ, f Φ' + ∇f × ψ'⟫` when `curl ψ' = Φ'` weakly (source 1351-1362). -/
def CurlMulGen : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ ψ' Φ' : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.HasPtwOp P curlT ψ' Φ' → LocL2 P ψ' → LocL2 P Φ' →
    ∀ f : Space → ℝ, SmF f → ∀ Ψ : ℝ × Space → CVec3, IsPhaseTest P Ψ →
      pairF P (fun x => f x.2 • curlT Ψ x) ψ' = pairF P Ψ (Vf f ψ' Φ')

/-- (K2) The weak gradient of a weak curl is a weak curl: `curl ∂ₖψ = ∂ₖΦ` weakly
(`pairF (curl Θ) (Dψ k) = pairF Θ (DΦ k)`), from `spΦ.grad`, `spΦ.curl`, `dΦ`. -/
def CurlOfGrad : Prop :=
  ∀ (P ν μ : ℝ) (D : TruncData), TruncHyp P ν μ D → ∀ k : Fin 3,
    UnforcedLeray.Short.IIb.HasPtwOp P curlT (D.Dψ k) (D.DΦ k)


/-- Pointwise commutator of `wOpT` with `χₙ` on smooth fields (source 1351-1362):
`χ wOpT Z = wOpT (χ Z) + (½ y·∇χ + νΔχ) Z + 2ν ∑ₖ ∂ₖχ ∂ₖ Z`. -/
theorem commutator_pt (ν μ : ℝ) (n : ℕ) {Z : ℝ × Space → CVec3} (hZ : ContDiff ℝ ∞ Z)
    (x : ℝ × Space) :
    cutχ n x.2 • wOpT ν μ Z x =
      wOpT ν μ (fun x => cutχ n x.2 • Z x) x +
      ((1 / 2 : ℝ) * radS (cutχ n) x.2 + ν * lapS (cutχ n) x.2) • Z x +
      ∑ k : Fin 3, ((2 * ν) * sd k (cutχ n) x.2) • dy k Z x := by
  have hc := contDiff_cutχ n
  have hda : Differentiable ℝ (cutχ n) := hc.differentiable (by simp)
  have hdZ : Differentiable ℝ Z := hZ.differentiable (by simp)
  have e : (fun x : ℝ × Space => cutχ n x.2 • Z x) = mulT (cutχ n) Z := rfl
  rw [e]
  simp only [wOpT, L0, T0]
  rw [congrFun (dτ_mulT hda hdZ) x, lapT_mulT_apply hc hZ x, radialT_mulT_apply hc hZ x]
  simp only [mulT, Fin.sum_univ_three, Complex.coe_smul, Pi.add_apply, Pi.sub_apply]
  module


theorem isPhaseTest_wOpT {P : ℝ} (ν μ : ℝ) {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (wOpT ν μ Θ) := by
  have h := ((UnforcedLeray.Short.IIb.isPhaseTest_L0 hΘ ν).add (hΘ.const_smul (μ : ℂ))).sub
    (hΘ.const_smul (1 / 2 : ℝ))
  exact h

theorem locL2_psi {P ν μ : ℝ} {D : TruncData} (hD : TruncHyp P ν μ D) : LocL2 P D.ψ :=
  Or.inr hD.spΦ.hardy

theorem locL2_Phi {P ν μ : ℝ} {D : TruncData} (hD : TruncHyp P ν μ D) : LocL2 P D.Φ :=
  Or.inl hD.dom.mem

theorem locL2_Dpsi {P ν μ : ℝ} {D : TruncData} (hD : TruncHyp P ν μ D) (k : Fin 3) :
    LocL2 P (D.Dψ k) := Or.inl (hD.spΦ.grad k).1

theorem locL2_DPhi {P ν μ : ℝ} {D : TruncData} (hD : TruncHyp P ν μ D) (k : Fin 3) :
    LocL2 P (D.DΦ k) := Or.inl (hD.dΦ k).1

/-- Weak integration by parts in `y` of `f ∂ₖ curl Ψ` against `ψ` (`spΦ.grad` on the phase test
`f curl Ψ`), then the weak curl move twice. -/
theorem ibp_step {P ν μ : ℝ} (hP : 0 < P) (h1 : CurlMulGen) (h2 : CurlOfGrad) {D : TruncData}
    (hD : TruncHyp P ν μ D) (k : Fin 3) {f : Space → ℝ} (hf : SmF f) {Ψ : ℝ × Space → CVec3}
    (hΨ : IsPhaseTest P Ψ) :
    pairF P (fun x => f x.2 • dy k (curlT Ψ) x) D.ψ =
      -pairF P Ψ (Vf f (D.Dψ k) (D.DΦ k)) - pairF P Ψ (Vf (sd k f) D.ψ D.Φ) := by
  have hZ := isPhaseTest_curlT hΨ
  have hΘ := isPhaseTest_smulF (P := P) hf hZ
  have hF := isPhaseTest_smulF (P := P) hf (hZ.dy k)
  have hG := isPhaseTest_smulF (P := P) (hf.sd k) hZ
  have hg := (hD.spΦ.grad k).2 _ hΘ
  have hpt : (-dy k (fun x : ℝ × Space => f x.2 • curlT Ψ x) : ℝ × Space → CVec3) =
      fun x => -((f x.2 • dy k (curlT Ψ) x) + (sd k f x.2 • curlT Ψ x)) := by
    have hd := dy_mulT (a := f) (hf.1.differentiable (by simp))
      (hZ.smooth.differentiable (by simp)) k
    funext x
    have := congrFun hd x
    simp only [mulT, Pi.add_apply] at this
    simp only [Pi.neg_apply]
    rw [show (fun x : ℝ × Space => f x.2 • curlT Ψ x) = mulT f (curlT Ψ) from rfl, this]
  have hg' : pairF P (fun x => -((f x.2 • dy k (curlT Ψ) x) + (sd k f x.2 • curlT Ψ x))) D.ψ =
      pairF P (fun x => f x.2 • curlT Ψ x) (D.Dψ k) := by
    rw [← hpt]; exact hg
  rw [pairF_neg_left, pairL_add_pt hP hF hG (locL2_psi hD)] at hg'
  have k1 := h1 P hP (D.Dψ k) (D.DΦ k) (h2 P ν μ D hD k) (locL2_Dpsi hD k) (locL2_DPhi hD k)
    f hf Ψ hΨ
  have k2 := h1 P hP D.ψ D.Φ hD.spΦ.curl (locL2_psi hD) (locL2_Phi hD) (sd k f) (hf.sd k) Ψ hΨ
  rw [k1] at hg'
  rw [← k2] at *
  linear_combination -hg'


/-! ### Scalar calculus and the identification of the error term -/

theorem sd_add' {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin 3)
    (y : Space) : sd j (fun y => f y + g y) y = sd j f y + sd j g y := by
  simp [UnforcedLeray.PhaseSpace.sd,
    fderiv_fun_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]

theorem sd_cmul' (c : ℝ) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 3) (y : Space) :
    sd j (fun y => c * f y) y = c * sd j f y := by
  simp [UnforcedLeray.PhaseSpace.sd, fderiv_const_mul (hf.differentiable (by simp) y)]

/-- `½ y·∇χ + νΔχ`. -/
def cA' (ν : ℝ) (n : ℕ) : Space → ℝ :=
  fun y => (1 / 2 : ℝ) * radS (cutχ n) y + ν * lapS (cutχ n) y

/-- `2ν ∂ₖχ`. -/
def cB (ν : ℝ) (n : ℕ) (k : Fin 3) : Space → ℝ := fun y => (2 * ν) * sd k (cutχ n) y

theorem smF_cA' (ν : ℝ) (n : ℕ) : SmF (cA' ν n) :=
  (((SmF.cut n).radS).const_mul _).add (((SmF.cut n).lapS).const_mul _)

theorem smF_cB (ν : ℝ) (n : ℕ) (k : Fin 3) : SmF (cB ν n k) :=
  (((SmF.cut n).sd k)).const_mul _

theorem sd_cA' (ν : ℝ) (n : ℕ) (j : Fin 3) (y : Space) :
    sd j (cA' ν n) y = 1 / 2 * sd j (radS (cutχ n)) y + ν * sd j (lapS (cutχ n)) y := by
  unfold cA'
  rw [sd_add' (((SmF.cut n).radS).const_mul _).1 (((SmF.cut n).lapS).const_mul _).1,
    sd_cmul' _ ((SmF.cut n).radS).1, sd_cmul' _ ((SmF.cut n).lapS).1]

theorem sd_cB (ν : ℝ) (n : ℕ) (j k : Fin 3) (y : Space) :
    sd j (cB ν n k) y = 2 * ν * sd j (sd k (cutχ n)) y := by
  unfold cB
  rw [sd_cmul' _ ((SmF.cut n).sd k).1]

theorem sd_sd_cB (ν : ℝ) (n : ℕ) (j k : Fin 3) (y : Space) :
    sd j (sd k (cB ν n k)) y = 2 * ν * sd j (sd k (sd k (cutχ n))) y := by
  have : sd k (cB ν n k) = fun y => (2 * ν) * sd k (sd k (cutχ n)) y := by
    funext z
    exact sd_cB ν n k k z
  rw [this, sd_cmul' _ (((SmF.cut n).sd k).sd k).1]

theorem lapS_cut_apply (n : ℕ) (y : Space) :
    lapS (cutχ n) y = sd 0 (sd 0 (cutχ n)) y + sd 1 (sd 1 (cutχ n)) y +
      sd 2 (sd 2 (cutχ n)) y := by
  simp [UnforcedLeray.PhaseSpace.lapS, Fin.sum_univ_three]

theorem sd_lapS_cut (n : ℕ) (j : Fin 3) (y : Space) :
    sd j (lapS (cutχ n)) y = sd j (sd 0 (sd 0 (cutχ n))) y + sd j (sd 1 (sd 1 (cutχ n))) y +
      sd j (sd 2 (sd 2 (cutχ n))) y := by
  have e : lapS (cutχ n) = fun y => (sd 0 (sd 0 (cutχ n)) y + sd 1 (sd 1 (cutχ n)) y) +
      sd 2 (sd 2 (cutχ n)) y := by
    funext z
    rw [lapS_cut_apply]
  have h0 := (((SmF.cut n).sd 0).sd 0).1
  have h1 := (((SmF.cut n).sd 1).sd 1).1
  have h2 := (((SmF.cut n).sd 2).sd 2).1
  rw [e, sd_add' (h0.add h1) h2, sd_add' h0 h1]

/-- The two-field term attached to `∂ₖ`. -/
def Uk (ν : ℝ) (n : ℕ) (D : TruncData) (k : Fin 3) : ℝ × Space → CVec3 :=
  fun x => Vf (cB ν n k) (D.Dψ k) (D.DΦ k) x + Vf (sd k (cB ν n k)) D.ψ D.Φ x

theorem E_eq (ν : ℝ) (n : ℕ) (D : TruncData) (x : ℝ × Space) :
    (EHardy n ν D x - crossC (gradC (cutχ n) x.2) (D.w x)) + EBdd n ν D x =
      Vf (cA' ν n) D.ψ D.Φ x + -Uk ν n D 0 x + -Uk ν n D 1 x + -Uk ν n D 2 x := by
  ext i
  fin_cases i <;>
  simp [Uk, Vf, EHardy, EBdd, crossC, gradC, Fin.sum_univ_three, cA', cB, sd_cA', sd_cB,
    sd_sd_cB, sd_lapS_cut, lapS_cut_apply, Complex.real_smul] <;> ring

theorem pair5 {P : ℝ} (hP : 0 < P) {A B C E F w : ℝ × Space → CVec3}
    (hA : IsPhaseTest P A) (hB : IsPhaseTest P B) (hC : IsPhaseTest P C) (hE : IsPhaseTest P E)
    (hF : IsPhaseTest P F) (hw : LocL2 P w) :
    pairF P (fun x => A x + B x + C x + E x + F x) w =
      pairF P A w + pairF P B w + pairF P C w + pairF P E w + pairF P F w := by
  have s1 : IsPhaseTest P (fun x => A x + B x) := hA.add hB
  have s2 : IsPhaseTest P (fun x => A x + B x + C x) := s1.add hC
  have s3 : IsPhaseTest P (fun x => A x + B x + C x + E x) := s2.add hE
  rw [pairL_add_pt hP s3 hF hw, pairL_add_pt hP s2 hE hw, pairL_add_pt hP s1 hC hw,
    pairL_add_pt hP hA hB hw]

theorem pair4R {P : ℝ} (hP : 0 < P) {Ψ X Y Z W : ℝ × Space → CVec3}
    (hX : Integrable (fun x => dotL (Ψ x) (X x)) (volume.restrict (phaseCell P)))
    (hY : Integrable (fun x => dotL (Ψ x) (Y x)) (volume.restrict (phaseCell P)))
    (hZ : Integrable (fun x => dotL (Ψ x) (Z x)) (volume.restrict (phaseCell P)))
    (hW : Integrable (fun x => dotL (Ψ x) (W x)) (volume.restrict (phaseCell P))) :
    pairF P Ψ (fun x => X x + Y x + Z x + W x) =
      pairF P Ψ X + pairF P Ψ Y + pairF P Ψ Z + pairF P Ψ W := by
  have addI : ∀ {X Y : ℝ × Space → CVec3},
      Integrable (fun x => dotL (Ψ x) (X x)) (volume.restrict (phaseCell P)) →
      Integrable (fun x => dotL (Ψ x) (Y x)) (volume.restrict (phaseCell P)) →
      Integrable (fun x => dotL (Ψ x) (X x + Y x)) (volume.restrict (phaseCell P)) :=
    fun hX hY => (hX.add hY).congr (ae_of_all _ fun x => by
      simp [dotL_apply, Finset.sum_add_distrib, mul_add])
  rw [pairR_add hP (addI (addI hX hY) hZ) hW, pairR_add hP (addI hX hY) hZ,
    pairR_add hP hX hY]


theorem intUk {P : ℝ} (hP : 0 < P) {ν μ : ℝ} {D : TruncData} (hD : TruncHyp P ν μ D) (n : ℕ)
    (k : Fin 3) {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) :
    Integrable (fun x => dotL (Ψ x) (Uk ν n D k x)) (volume.restrict (phaseCell P)) := by
  have h1 := intV hP (smF_cB ν n k) hΨ (locL2_Dpsi hD k) (locL2_DPhi hD k)
  have h2 := intV hP ((smF_cB ν n k).sd k) hΨ (locL2_psi hD) (locL2_Phi hD)
  refine (h1.add h2).congr (ae_of_all _ fun x => ?_)
  simp [Uk, dotL_apply, Finset.sum_add_distrib, mul_add]

theorem pairUk {P : ℝ} (hP : 0 < P) {ν μ : ℝ} {D : TruncData} (hD : TruncHyp P ν μ D) (n : ℕ)
    (k : Fin 3) {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) :
    pairF P Ψ (Uk ν n D k) =
      pairF P Ψ (Vf (cB ν n k) (D.Dψ k) (D.DΦ k)) +
        pairF P Ψ (Vf (sd k (cB ν n k)) D.ψ D.Φ) :=
  pairR_add hP (intV hP (smF_cB ν n k) hΨ (locL2_Dpsi hD k) (locL2_DPhi hD k))
    (intV hP ((smF_cB ν n k).sd k) hΨ (locL2_psi hD) (locL2_Phi hD))

/-- **`TruncCommutator`** from the two weak-curl lemmas (source 1334-1337, 1351-1362, 1470-1480). -/
theorem truncCommutator_of (h1 : CurlMulGen) (h2 : CurlOfGrad) : TruncCommutator := by
  intro hCut P ν μ hP hP1 hν hμ D hD n Ψ hΨ
  have hZ := isPhaseTest_curlT hΨ
  have hA : IsPhaseTest P (wOpT ν μ (fun x => cutχ n x.2 • curlT Ψ x)) :=
    isPhaseTest_wOpT ν μ (isPhaseTest_smulF (SmF.cut n) hZ)
  have hTa : IsPhaseTest P (fun x => cA' ν n x.2 • curlT Ψ x) :=
    isPhaseTest_smulF (smF_cA' ν n) hZ
  have hT : ∀ k : Fin 3, IsPhaseTest P (fun x => cB ν n k x.2 • dy k (curlT Ψ) x) :=
    fun k => isPhaseTest_smulF (smF_cB ν n k) (hZ.dy k)
  have hfun : (fun x : ℝ × Space => cutχ n x.2 • wOpT ν μ (curlT Ψ) x) =
      fun x => wOpT ν μ (fun x => cutχ n x.2 • curlT Ψ x) x + cA' ν n x.2 • curlT Ψ x +
        cB ν n 0 x.2 • dy 0 (curlT Ψ) x + cB ν n 1 x.2 • dy 1 (curlT Ψ) x +
        cB ν n 2 x.2 • dy 2 (curlT Ψ) x := by
    funext x
    rw [commutator_pt ν μ n hZ.smooth x]
    simp only [Fin.sum_univ_three, cA', cB]
    abel
  rw [hfun, pair5 hP hA hTa (hT 0) (hT 1) (hT 2) (locL2_psi hD)]
  have key : ∀ k : Fin 3, pairF P (fun x => cB ν n k x.2 • dy k (curlT Ψ) x) D.ψ =
      -pairF P Ψ (Uk ν n D k) := fun k => by
    rw [ibp_step hP h1 h2 hD k (smF_cB ν n k) hΨ, pairUk hP hD n k hΨ]
    ring
  have ka := h1 P hP D.ψ D.Φ hD.spΦ.curl (locL2_psi hD) (locL2_Phi hD) (cA' ν n) (smF_cA' ν n)
    Ψ hΨ
  have hE : (fun x : ℝ × Space => (EHardy n ν D x - crossC (gradC (cutχ n) x.2) (D.w x)) +
      EBdd n ν D x) = fun x => Vf (cA' ν n) D.ψ D.Φ x + -Uk ν n D 0 x + -Uk ν n D 1 x +
        -Uk ν n D 2 x := funext (E_eq ν n D)
  have negI : ∀ k : Fin 3, Integrable (fun x => dotL (Ψ x) ((fun x => -Uk ν n D k x) x))
      (volume.restrict (phaseCell P)) := fun k =>
    (intUk hP hD n k hΨ).neg.congr (ae_of_all _ fun x => by simp [dotL_apply])
  have hR := pair4R hP (intV hP (smF_cA' ν n) hΨ (locL2_psi hD) (locL2_Phi hD)) (negI 0) (negI 1)
    (negI 2)
  rw [hE, hR, pairF_neg_right, pairF_neg_right, pairF_neg_right, key 0, key 1, key 2, ka]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
