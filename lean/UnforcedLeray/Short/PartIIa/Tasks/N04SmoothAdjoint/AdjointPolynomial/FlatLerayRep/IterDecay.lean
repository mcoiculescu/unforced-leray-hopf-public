import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_1
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!


Source of record: `the November 2 reference manuscript`,
lines 1723–1726 and 1800–1823 (Lemma `near:adjoint-polynomial`).

Proves `theorem flatLerayIterDecay : FlatLerayIterDecay` in namespace `UnforcedLeray.Short.PartIIa`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

namespace IterDecayAux

/-- Exponential `|η|`-decay predicate on profile functions. -/
def HasExpEtaDecay (g : Profile → ℝ) : Prop :=
  ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ p : Profile, g p ≤ C * Real.exp (-(κ * |p.2.2|))

lemma hasExpEtaDecay_zero : HasExpEtaDecay (fun _ => 0) :=
  ⟨0, 1, le_rfl, one_pos, fun p => by simp⟩

lemma HasExpEtaDecay.mono {g₁ g₂ : Profile → ℝ} (h₂ : HasExpEtaDecay g₂)
    (hle : ∀ p, g₁ p ≤ g₂ p) : HasExpEtaDecay g₁ := by
  obtain ⟨C, κ, hC, hκ, hdec⟩ := h₂
  exact ⟨C, κ, hC, hκ, fun p => (hle p).trans (hdec p)⟩

lemma HasExpEtaDecay.add {g₁ g₂ : Profile → ℝ} (h₁ : HasExpEtaDecay g₁)
    (h₂ : HasExpEtaDecay g₂) : HasExpEtaDecay (fun p => g₁ p + g₂ p) := by
  obtain ⟨C₁, κ₁, hC₁, hκ₁, hd₁⟩ := h₁
  obtain ⟨C₂, κ₂, hC₂, hκ₂, hd₂⟩ := h₂
  refine ⟨C₁ + C₂, min κ₁ κ₂, add_nonneg hC₁ hC₂, lt_min hκ₁ hκ₂, fun p => ?_⟩
  have h1 : Real.exp (-(κ₁ * |p.2.2|)) ≤ Real.exp (-(min κ₁ κ₂ * |p.2.2|)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left κ₁ κ₂) (abs_nonneg p.2.2)
    linarith
  have h2 : Real.exp (-(κ₂ * |p.2.2|)) ≤ Real.exp (-(min κ₁ κ₂ * |p.2.2|)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right κ₁ κ₂) (abs_nonneg p.2.2)
    linarith
  calc g₁ p + g₂ p
      ≤ C₁ * Real.exp (-(κ₁ * |p.2.2|)) + C₂ * Real.exp (-(κ₂ * |p.2.2|)) :=
        add_le_add (hd₁ p) (hd₂ p)
    _ ≤ C₁ * Real.exp (-(min κ₁ κ₂ * |p.2.2|)) +
          C₂ * Real.exp (-(min κ₁ κ₂ * |p.2.2|)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC₁) (mul_le_mul_of_nonneg_left h2 hC₂)
    _ = (C₁ + C₂) * Real.exp (-(min κ₁ κ₂ * |p.2.2|)) := by ring

lemma hasExpEtaDecay_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Profile → ℝ)
    (hf : ∀ k ∈ s, HasExpEtaDecay (f k)) :
    HasExpEtaDecay (fun p => ∑ k ∈ s, f k p) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasExpEtaDecay_zero
  | @insert a s ha ih =>
    have h1 : HasExpEtaDecay (f a) := hf a (Finset.mem_insert_self a s)
    have h2 : HasExpEtaDecay (fun p => ∑ k ∈ s, f k p) :=
      ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    refine (h1.add h2).mono fun p => ?_
    rw [Finset.sum_insert ha]

lemma hasExpEtaDecay_lerayField {c : ℝ} (hc : 0 < c) {F : Chart → Fin 2 → ℝ}
    (hF : IsForceField c F) (i : Fin 2) :
    HasExpEtaDecay (fun p => |lerayField c F p i|) := by
  obtain ⟨C, κ, hκ, hdec⟩ := (lerayFieldProps c hc F hF).2.2.2.2.1
  refine ⟨max C 0, κ, le_max_right C 0, hκ, fun p => ?_⟩
  exact (hdec p i).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _))

/-- Symmetry of second directional derivatives for smooth chart functions. -/
lemma fderiv_apply_comm {f : Chart → ℝ} (hf : ContDiff ℝ ∞ f) (u v p : Chart) :
    fderiv ℝ (fun q => fderiv ℝ f q u) p v = fderiv ℝ (fun q => fderiv ℝ f q v) p u := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) p
  have hu : HasFDerivAt (fun q => fderiv ℝ f q u)
      ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ f) p)) p :=
    (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp p hD.hasFDerivAt
  have hv : HasFDerivAt (fun q => fderiv ℝ f q v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) p)) p :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp p hD.hasFDerivAt
  rw [hu.fderiv, hv.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq v u

lemma dfDv_comm {F : Chart → Fin 2 → ℝ} (hFs : ∀ i, ContDiff ℝ ∞ (fun p => F p i))
    (u v : Chart) :
    dfDv (dfDv F u) v = dfDv (dfDv F v) u := by
  funext p i
  exact fderiv_apply_comm (hFs i) u v p

/-- `lerayField c` commutes with constant-coefficient directional derivatives `dfDv`. -/
lemma dfDv_lerayField {c : ℝ} (hc : 0 < c) {F : Chart → Fin 2 → ℝ} (hF : IsForceField c F)
    (v : Chart) :
    dfDv (lerayField c F) v = lerayField c (dfDv F v) := by
  funext p i
  have hGi : IsForceField c (dfDv F (lfpDir i)) := forceFieldDeriv c F hF (lfpDir i)
  have hFv : IsForceField c (dfDv F v) := forceFieldDeriv c F hF v
  have hflat : ∀ (G : Chart → Fin 2 → ℝ), IsForceField c G → ∀ q : Chart,
      flatGrad (lerayPot c G) q i = lerayPot c (dfDv G (lfpDir i)) q := by
    intro G hG q
    fin_cases i
    · exact (lerayPotSmooth c hc G hG).2.2 q (lfpDir 0)
    · exact (lerayPotSmooth c hc G hG).2.2 q (lfpDir 1)
  have hL : (fun q : Chart => lerayField c F q i) =
      fun q => F q i - lerayPot c (dfDv F (lfpDir i)) q := by
    funext q
    show F q i - flatGrad (lerayPot c F) q i = F q i - lerayPot c (dfDv F (lfpDir i)) q
    rw [hflat F hF q]
  have hd1 : HasFDerivAt (fun q : Chart => F q i) (fderiv ℝ (fun q => F q i) p) p :=
    (((hF.1 i).differentiable (by simp)) p).hasFDerivAt
  have hd2 : HasFDerivAt (lerayPot c (dfDv F (lfpDir i)))
      (fderiv ℝ (lerayPot c (dfDv F (lfpDir i))) p) p :=
    (((lerayPotSmooth c hc _ hGi).1.differentiable (by simp)) p).hasFDerivAt
  have hsub : fderiv ℝ (fun q : Chart => F q i - lerayPot c (dfDv F (lfpDir i)) q) p =
      fderiv ℝ (fun q => F q i) p - fderiv ℝ (lerayPot c (dfDv F (lfpDir i))) p :=
    (hd1.sub hd2).fderiv
  change fderiv ℝ (fun q => lerayField c F q i) p v =
    dfDv F v p i - flatGrad (lerayPot c (dfDv F v)) p i
  rw [hL, hsub]
  have hpot_v : fderiv ℝ (lerayPot c (dfDv F (lfpDir i))) p v =
      lerayPot c (dfDv (dfDv F (lfpDir i)) v) p :=
    (lerayPotSmooth c hc (dfDv F (lfpDir i)) hGi).2.2 p v
  change fderiv ℝ (fun q => F q i) p v - fderiv ℝ (lerayPot c (dfDv F (lfpDir i))) p v = _
  rw [hpot_v, dfDv_comm hF.1 (lfpDir i) v, hflat (dfDv F v) hFv p]
  rfl

/-- Multiplication of a real chart field by age `s = p.1`. -/
def sMul (F : Chart → Fin 2 → ℝ) : Chart → Fin 2 → ℝ :=
  fun p i => p.1 * F p i

lemma isForceField_sMul {c : ℝ} {F : Chart → Fin 2 → ℝ} (hF : IsForceField c F) :
    IsForceField c (sMul F) := by
  obtain ⟨hFs, hFp, s0, s1, L, hs0, hFb⟩ := hF
  refine ⟨fun i => contDiff_fst.mul (hFs i), fun s q η => ?_, ⟨s0, s1, L, hs0, fun p hp => ?_⟩⟩
  · funext i
    simp [sMul, congrFun (hFp s q η) i]
  · apply hFb p
    intro h0
    apply hp
    funext i
    simp [sMul, h0]

lemma dfDv_sMul_of_fst_eq_zero {F : Chart → Fin 2 → ℝ}
    (hFs : ∀ i, ContDiff ℝ ∞ (fun p => F p i)) {u : Chart} (hu : u.1 = 0) :
    dfDv (sMul F) u = sMul (dfDv F u) := by
  funext p i
  have hd1 : HasFDerivAt (fun q : Chart => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have hd2 : HasFDerivAt (fun q : Chart => F q i) (fderiv ℝ (fun q => F q i) p) p :=
    (((hFs i).differentiable (by simp)) p).hasFDerivAt
  have hmul : fderiv ℝ (fun q : Chart => q.1 * F q i) p =
      p.1 • fderiv ℝ (fun q => F q i) p + F p i • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) :=
    (hd1.mul hd2).fderiv
  change fderiv ℝ (fun q : Chart => q.1 * F q i) p u = p.1 * fderiv ℝ (fun q => F q i) p u
  rw [hmul]
  simp [hu]

lemma lerayPot_sMul (c : ℝ) (G : Chart → Fin 2 → ℝ) (p : Chart) :
    lerayPot c (sMul G) p = p.1 * lerayPot c G p := by
  unfold lerayPot sMul
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  ring

lemma lerayField_sMul {c : ℝ} (hc : 0 < c) {F : Chart → Fin 2 → ℝ} (hF : IsForceField c F) :
    lerayField c (sMul F) = sMul (lerayField c F) := by
  funext p i
  have hSF : IsForceField c (sMul F) := isForceField_sMul hF
  have hu : (lfpDir i).1 = 0 := by fin_cases i <;> rfl
  have hflat1 : flatGrad (lerayPot c (sMul F)) p i = lerayPot c (dfDv (sMul F) (lfpDir i)) p := by
    fin_cases i
    · exact (lerayPotSmooth c hc (sMul F) hSF).2.2 p (lfpDir 0)
    · exact (lerayPotSmooth c hc (sMul F) hSF).2.2 p (lfpDir 1)
  have hflat2 : flatGrad (lerayPot c F) p i = lerayPot c (dfDv F (lfpDir i)) p := by
    fin_cases i
    · exact (lerayPotSmooth c hc F hF).2.2 p (lfpDir 0)
    · exact (lerayPotSmooth c hc F hF).2.2 p (lfpDir 1)
  show sMul F p i - flatGrad (lerayPot c (sMul F)) p i =
    p.1 * (F p i - flatGrad (lerayPot c F) p i)
  rw [hflat1, hflat2, dfDv_sMul_of_fst_eq_zero hF.1 hu, lerayPot_sMul]
  simp only [sMul]
  ring

/-- Age scaling operator `S = s ∂_s` on real chart fields `Chart → Fin 2 → ℝ`. -/
def opSF (F : Chart → Fin 2 → ℝ) : Chart → Fin 2 → ℝ :=
  sMul (dfDv F (1, 0, 0))

lemma isForceField_opSF_iter {c : ℝ} {F : Chart → Fin 2 → ℝ} (hF : IsForceField c F) :
    ∀ a : ℕ, IsForceField c (opSF^[a] F)
  | 0 => hF
  | a + 1 => by
    rw [Function.iterate_succ']
    exact isForceField_sMul (forceFieldDeriv c _ (isForceField_opSF_iter hF a) (1, 0, 0))

lemma opSF_iter_lerayField {c : ℝ} (hc : 0 < c) {F : Chart → Fin 2 → ℝ}
    (hF : IsForceField c F) :
    ∀ a : ℕ, opSF^[a] (lerayField c F) = lerayField c (opSF^[a] F)
  | 0 => rfl
  | a + 1 => by
    rw [Function.iterate_succ', Function.comp_apply, Function.comp_apply,
      opSF_iter_lerayField hc hF a]
    have hFa : IsForceField c (opSF^[a] F) := isForceField_opSF_iter hF a
    change sMul (dfDv (lerayField c (opSF^[a] F)) (1, 0, 0)) =
      lerayField c (sMul (dfDv (opSF^[a] F) (1, 0, 0)))
    rw [dfDv_lerayField hc hFa (1, 0, 0)]
    exact (lerayField_sMul hc (forceFieldDeriv c _ hFa (1, 0, 0))).symm

/-- Iterated directional derivative of a real chart field along a tuple `Fin m → Chart`. -/
def iterDF : ∀ (m : ℕ), (Fin m → Chart) → (Chart → Fin 2 → ℝ) → (Chart → Fin 2 → ℝ)
  | 0, _, F => F
  | m + 1, g, F => dfDv (iterDF m (fun k => g k.succ) F) (g 0)

lemma isForceField_iterDF {c : ℝ} :
    ∀ (m : ℕ) (g : Fin m → Chart) {F : Chart → Fin 2 → ℝ},
      IsForceField c F → IsForceField c (iterDF m g F)
  | 0, _, _, hF => hF
  | m + 1, g, _, hF =>
      forceFieldDeriv c _ (isForceField_iterDF m (fun k => g k.succ) hF) (g 0)

lemma iterDF_lerayField {c : ℝ} (hc : 0 < c) :
    ∀ (m : ℕ) (g : Fin m → Chart) {F : Chart → Fin 2 → ℝ},
      IsForceField c F → iterDF m g (lerayField c F) = lerayField c (iterDF m g F)
  | 0, _, _, _ => rfl
  | m + 1, g, _, hF => by
      simp only [iterDF, iterDF_lerayField hc m (fun k => g k.succ) hF]
      exact dfDv_lerayField hc (isForceField_iterDF m (fun k => g k.succ) hF) (g 0)

lemma iterDF_eq_iteratedFDeriv_apply (W : Chart → Fin 2 → ℝ)
    (hWs : ∀ i, ContDiff ℝ ∞ (fun p => W p i)) :
    ∀ (m : ℕ) (g : Fin m → Chart) (p : Chart) (i : Fin 2),
      iterDF m g W p i = iteratedFDeriv ℝ m (fun q => W q i) p g
  | 0, g, p, i => by
      simp [iterDF, iteratedFDeriv_zero_apply]
  | m + 1, g, p, i => by
      have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ m (fun q => W q i)) :=
        (hWs i).iteratedFDeriv_right (m := ∞) (i := m) (by simp)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun q => W q i)) p :=
        (hD.differentiable (by simp)) p
      have heq : (fun q => iterDF m (fun k => g k.succ) W q i) =
          fun q => iteratedFDeriv ℝ m (fun q' => W q' i) q (fun k => g k.succ) :=
        funext fun q => iterDF_eq_iteratedFDeriv_apply W hWs m (fun k => g k.succ) q i
      change fderiv ℝ (fun q => iterDF m (fun k => g k.succ) W q i) p (g 0) = _
      rw [heq, iteratedFDeriv_succ_apply_left]
      exact fderiv_continuousMultilinear_apply_const_apply hdiff (fun k => g k.succ) (g 0)

/-- Real and imaginary coordinate projections on `MeridC` as continuous `ℝ`-linear maps. -/
def projReCLM (i : Fin 2) : MeridC →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)

def projImCLM (i : Fin 2) : MeridC →L[ℝ] ℝ :=
  Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)

lemma projReCLM_flatLerayRep (c : ℝ) (z : Profile → MeridC) (p : Profile) (i : Fin 2) :
    projReCLM i (flatLerayRep c z p) = lerayField c (meridReField z) p i := by
  simp [projReCLM, flatLerayRep, cvec]

lemma projImCLM_flatLerayRep (c : ℝ) (z : Profile → MeridC) (p : Profile) (i : Fin 2) :
    projImCLM i (flatLerayRep c z p) = lerayField c (meridImField z) p i := by
  simp [projImCLM, flatLerayRep, cvec]

lemma norm_meridC_le_sum_proj (w : MeridC) :
    ‖w‖ ≤ ∑ i : Fin 2, (|projReCLM i w| + |projImCLM i w|) := by
  have hsq : ‖w‖ ^ 2 ≤ (∑ i : Fin 2, ‖w i‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_two]
    nlinarith [norm_nonneg (w 0), norm_nonneg (w 1)]
  have h1 : ‖w‖ ≤ ∑ i : Fin 2, ‖w i‖ :=
    (abs_le_of_sq_le_sq' hsq (Finset.sum_nonneg fun i _ => norm_nonneg _)).2
  refine h1.trans (Finset.sum_le_sum fun i _ => ?_)
  simpa [projReCLM, projImCLM] using Complex.norm_le_abs_re_add_abs_im (w i)

lemma contDiff_opS_iter {h : Profile → MeridC} (hh : ContDiff ℝ ∞ h) :
    ∀ a : ℕ, ContDiff ℝ ∞ (opS^[a] h)
  | 0 => hh
  | a + 1 => by
      rw [Function.iterate_succ']
      unfold opS pdS
      exact contDiff_fst.smul (((contDiff_opS_iter hh a).fderiv_right (by simp)).clm_apply
        contDiff_const)

lemma clm_opS_iter_eq_opSF_iter (L : MeridC →L[ℝ] ℝ) {h : Profile → MeridC}
    (hh : ContDiff ℝ ∞ h) {W : Chart → Fin 2 → ℝ} (i : Fin 2)
    (hLW : ∀ p : Profile, L (h p) = W p i) :
    ∀ (a : ℕ) (p : Profile), L ((opS^[a] h) p) = (opSF^[a] W) p i
  | 0, p => hLW p
  | a + 1, p => by
      rw [Function.iterate_succ', Function.iterate_succ']
      have hha : DifferentiableAt ℝ (opS^[a] h) p :=
        ((contDiff_opS_iter hh a).differentiable (by simp)) p
      have hcomp : HasFDerivAt (fun q => L ((opS^[a] h) q))
          (L.comp (fderiv ℝ (opS^[a] h) p)) p :=
        L.hasFDerivAt.comp p hha.hasFDerivAt
      have hfun : (fun q => L ((opS^[a] h) q)) = fun q => (opSF^[a] W) q i :=
        funext (clm_opS_iter_eq_opSF_iter L hh i hLW a)
      change L (p.1 • fderiv ℝ (opS^[a] h) p (1, 0, 0)) =
        p.1 * fderiv ℝ (fun q => (opSF^[a] W) q i) p (1, 0, 0)
      rw [map_smul, smul_eq_mul, ← hfun, hcomp.fderiv]
      rfl

lemma contDiff_opSF_iter {W : Chart → Fin 2 → ℝ}
    (hWs : ∀ j, ContDiff ℝ ∞ (fun p => W p j)) :
    ∀ (a : ℕ) (j : Fin 2), ContDiff ℝ ∞ (fun q => (opSF^[a] W) q j)
  | 0, j => hWs j
  | a + 1, j => by
      rw [Function.iterate_succ']
      exact contDiff_fst.mul (((contDiff_opSF_iter hWs a j).fderiv_right (by simp)).clm_apply
        contDiff_const)

lemma clm_iteratedFDeriv_opS_eq_iterDF (L : MeridC →L[ℝ] ℝ) {h : Profile → MeridC}
    (hh : ContDiff ℝ ∞ h) {W : Chart → Fin 2 → ℝ}
    (hWs : ∀ j, ContDiff ℝ ∞ (fun p => W p j)) (i : Fin 2)
    (hLW : ∀ p : Profile, L (h p) = W p i)
    (a m : ℕ) (g : Fin m → Chart) (p : Profile) :
    L (iteratedFDeriv ℝ m (opS^[a] h) p g) = iterDF m g (opSF^[a] W) p i := by
  have hha : ContDiffAt ℝ ∞ (opS^[a] h) p := (contDiff_opS_iter hh a).contDiffAt
  have hcomp := L.iteratedFDeriv_comp_left hha (i := m) (by simp)
  have hfun : L ∘ (opS^[a] h) = fun q => (opSF^[a] W) q i :=
    funext (clm_opS_iter_eq_opSF_iter L hh i hLW a)
  have hWa : ∀ j, ContDiff ℝ ∞ (fun q => (opSF^[a] W) q j) := contDiff_opSF_iter hWs a
  calc L (iteratedFDeriv ℝ m (opS^[a] h) p g)
      = (L.compContinuousMultilinearMap (iteratedFDeriv ℝ m (opS^[a] h) p)) g := rfl
    _ = iteratedFDeriv ℝ m (L ∘ (opS^[a] h)) p g := by rw [← hcomp]
    _ = iteratedFDeriv ℝ m (fun q => (opSF^[a] W) q i) p g := by rw [hfun]
    _ = iterDF m g (opSF^[a] W) p i :=
        (iterDF_eq_iteratedFDeriv_apply (opSF^[a] W) hWa m g p i).symm

/-- Standard coordinate basis of `Profile = ℝ × ℝ × ℝ`. -/
def profDir (j : Fin 3) : Profile :=
  ![((1 : ℝ), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ), (1 : ℝ))] j

/-- Operator-norm bound on `ContinuousMultilinearMap ℝ (fun _ : Fin m => Profile) MeridC`
by evaluation on standard basis tuples. -/
lemma norm_multilinear_profile_le (m : ℕ)
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin m => Profile) MeridC) :
    ‖D‖ ≤ ∑ r : Fin m → Fin 3, ‖D (fun k => profDir (r k))‖ := by
  set c : Fin 3 → Profile → ℝ := fun j y => ![y.1, y.2.1, y.2.2] j with hcdef
  have hexp : ∀ y : Profile, y = ∑ j : Fin 3, c j y • profDir j := by
    intro y
    ext <;> simp [hcdef, profDir, Fin.sum_univ_three]
  have hc : ∀ (j : Fin 3) (y : Profile), ‖c j y‖ ≤ ‖y‖ := by
    intro j y
    fin_cases j
    · exact norm_fst_le y
    · exact (norm_fst_le y.2).trans (norm_snd_le y)
    · exact (norm_snd_le y.2).trans (norm_snd_le y)
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hD : D v = ∑ r : Fin m → Fin 3, (∏ k, c (r k) (v k)) • D (fun k => profDir (r k)) := by
    have hv : v = fun k => ∑ j : Fin 3, c j (v k) • profDir j := funext fun k => hexp (v k)
    conv_lhs => rw [hv]
    rw [ContinuousMultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun r _ =>
      ContinuousMultilinearMap.map_smul_univ D (fun k => c (r k) (v k)) (fun k => profDir (r k))
  calc ‖D v‖
      = ‖∑ r : Fin m → Fin 3, (∏ k, c (r k) (v k)) • D (fun k => profDir (r k))‖ := by rw [hD]
    _ ≤ ∑ r : Fin m → Fin 3, ‖(∏ k, c (r k) (v k)) • D (fun k => profDir (r k))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r : Fin m → Fin 3, (∏ k, ‖v k‖) * ‖D (fun k => profDir (r k))‖ := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_smul, norm_prod]
        exact mul_le_mul_of_nonneg_right
          (Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => hc _ _) (norm_nonneg _)
    _ = (∑ r : Fin m → Fin 3, ‖D (fun k => profDir (r k))‖) * ∏ k, ‖v k‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => mul_comm _ _

end IterDecayAux

open IterDecayAux in
/-- **Exponential `η`-decay of iterated derivatives of `opS^[a] (flatLerayRep c z)`
(`FlatLerayIterDecay`, task `PartII-a:N04/2/1/1`).** -/
theorem flatLerayIterDecay : FlatLerayIterDecay := by
  intro c σ H1 L1 hc hσ _ _ z hz hsupp a _ m _
  have hRe : IsForceField c (meridReField z) := isForceField_meridReField hσ hz hsupp
  have hIm : IsForceField c (meridImField z) := isForceField_meridImField hσ hz hsupp
  have hsm : ContDiff ℝ ∞ (flatLerayRep c z) := flatLerayRep_smooth hc hσ hz hsupp
  have hWRe : ∀ j, ContDiff ℝ ∞ (fun p => lerayField c (meridReField z) p j) :=
    (lerayFieldProps c hc _ hRe).1
  have hWIm : ∀ j, ContDiff ℝ ∞ (fun p => lerayField c (meridImField z) p j) :=
    (lerayFieldProps c hc _ hIm).1
  have hsum_decay :
      HasExpEtaDecay (fun p : Profile =>
        ∑ r : Fin m → Fin 3, ∑ i : Fin 2,
          (|projReCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p
              (fun k => profDir (r k)))| +
            |projImCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p
              (fun k => profDir (r k)))|)) := by
    refine hasExpEtaDecay_sum Finset.univ _ fun r _ => ?_
    refine hasExpEtaDecay_sum Finset.univ _ fun i _ => ?_
    set g : Fin m → Chart := fun k => profDir (r k)
    have hRe_eq : ∀ p : Profile,
        projReCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p g) =
          lerayField c (iterDF m g (opSF^[a] (meridReField z))) p i := by
      intro p
      rw [clm_iteratedFDeriv_opS_eq_iterDF (projReCLM i) hsm hWRe i
        (fun q => projReCLM_flatLerayRep c z q i) a m g p,
        opSF_iter_lerayField hc hRe a,
        iterDF_lerayField hc m g (isForceField_opSF_iter hRe a)]
    have hIm_eq : ∀ p : Profile,
        projImCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p g) =
          lerayField c (iterDF m g (opSF^[a] (meridImField z))) p i := by
      intro p
      rw [clm_iteratedFDeriv_opS_eq_iterDF (projImCLM i) hsm hWIm i
        (fun q => projImCLM_flatLerayRep c z q i) a m g p,
        opSF_iter_lerayField hc hIm a,
        iterDF_lerayField hc m g (isForceField_opSF_iter hIm a)]
    have hGRe : IsForceField c (iterDF m g (opSF^[a] (meridReField z))) :=
      isForceField_iterDF m g (isForceField_opSF_iter hRe a)
    have hGIm : IsForceField c (iterDF m g (opSF^[a] (meridImField z))) :=
      isForceField_iterDF m g (isForceField_opSF_iter hIm a)
    have hdRe : HasExpEtaDecay
        (fun p => |projReCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p g)|) :=
      (hasExpEtaDecay_lerayField hc hGRe i).mono fun p => by rw [hRe_eq p]
    have hdIm : HasExpEtaDecay
        (fun p => |projImCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p g)|) :=
      (hasExpEtaDecay_lerayField hc hGIm i).mono fun p => by rw [hIm_eq p]
    exact hdRe.add hdIm
  refine hsum_decay.mono fun p => ?_
  calc ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖
      ≤ ∑ r : Fin m → Fin 3,
          ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (fun k => profDir (r k))‖ :=
        norm_multilinear_profile_le m _
    _ ≤ ∑ r : Fin m → Fin 3, ∑ i : Fin 2,
          (|projReCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p
              (fun k => profDir (r k)))| +
            |projImCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p
              (fun k => profDir (r k)))|) :=
        Finset.sum_le_sum fun r _ => norm_meridC_le_sum_proj _

end UnforcedLeray.Short.PartIIa
