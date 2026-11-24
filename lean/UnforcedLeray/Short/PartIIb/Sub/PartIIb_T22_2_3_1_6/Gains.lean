import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.HeatOps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCommute
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.BandBounded
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CylTestBounded

/-!

`CommGain`

Source: `the November 2 reference manuscript`, lines 2085-2093 and 2100-2105.  The
last four are applications of the abstract calculus of `DConv.lean` to the heat operators of
`HeatOps.lean`; `GainOne` differentiates through `∂_j K_a * g = K_a * ∂_j g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

variable {T : ℝ}

/-! ## The generic Duhamel classes -/

/-- The Volterra bound is uniformly bounded in `σ`. -/
theorem Kconv_bdd {K : ℝ} {b : ℝ → ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T)) :
    ∃ C : ℝ, ∀ σ ∈ Icc 0 T, Kconv K b σ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hb
  have hbM : ∀ r ∈ Icc 0 T, b r ≤ M := fun r hr =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM r hr)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  refine ⟨K * (M * (T + 2 * T ^ (1 / 2 : ℝ))), fun σ hσ => ?_⟩
  unfold Kconv
  refine mul_le_mul_of_nonneg_left ?_ hK
  have hle : (∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * b r) ≤
      ∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * M := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hσ.1 (kInt_mul hb hσ)
      (kInt_mul continuousOn_const hσ) fun r hr => ?_
    have h1 : 0 ≤ (σ - r) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith [hr.2]) _
    exact mul_le_mul_of_nonneg_left (hbM r ⟨hr.1.le, hr.2.le.trans hσ.2⟩) (by linarith)
  refine hle.trans ?_
  have hval : (∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * M) =
      M * (σ + 2 * σ ^ (1 / 2 : ℝ)) := by
    have e : ∀ r : ℝ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * M = M * (1 + (σ - r) ^ (-(1 / 2 : ℝ))) :=
      fun r => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      intervalIntegrable_const (UnforcedLeray.Gronwall.intervalIntegrable_kernel σ 0 σ),
      UnforcedLeray.Gronwall.integral_kernel_rpow]
    simp
  rw [hval]
  refine mul_le_mul_of_nonneg_left ?_ hM0
  have h2 : σ ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hσ.1 hσ.2 (by norm_num)
  linarith [hσ.2]

theorem dConv_cb0 {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hb : ContinuousOn b (Icc 0 T)) (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A) :
    CB0 T (dConv ν A) := by
  have hK : 0 ≤ C * (1 + ν ^ (-(1 / 2 : ℝ))) :=
    mul_nonneg hC (add_nonneg zero_le_one (Real.rpow_nonneg hν.le _))
  obtain ⟨M, hM⟩ := Kconv_bdd hK hT hb
  exact ⟨dConv_cont hν hC hT hb hb0 hA, M, fun σ hσ x =>
    (dConv_le hν hC hb hb0 hA hσ x).trans (hM σ hσ)⟩

theorem dConv_pd_all {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} {Aj : Fin 2 → ℝ → ℝ → Pl → ℝ}
    (hν : 0 < ν) (hC : 0 ≤ C) (hb : ContinuousOn b (Icc 0 T)) (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r)
    (hA : DAdm T C b A) (hAj : ∀ j, DAdm T C b (Aj j))
    (hd : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (A a r)
      (Aj 0 a r x • ContinuousLinearMap.fst ℝ ℝ ℝ + Aj 1 a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    {σ : ℝ} (hσ : σ ∈ Icc 0 T) (j : Fin 2) (x : Pl) :
    B0579.pd j (dConv ν A σ) x = dConv ν (Aj j) σ x := by
  have h := dConv_pd hν hC hb hb0 hA (hAj 0) (hAj 1) hd hσ x
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · exact h.1
  · exact h.2

/-- The class of a Duhamel integral with one derivative. -/
theorem dConv_CB1 {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} {Aj : Fin 2 → ℝ → ℝ → Pl → ℝ}
    (hν : 0 < ν) (hC : 0 ≤ C) (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T))
    (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A) (hAj : ∀ j, DAdm T C b (Aj j))
    (hd : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (A a r)
      (Aj 0 a r x • ContinuousLinearMap.fst ℝ ℝ ℝ + Aj 1 a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) :
    CB T 1 (dConv ν A) ∧ CBle T 1 (dConv ν A) (Kconv (C * (1 + ν ^ (-(1 / 2 : ℝ)))) b) := by
  have hp := fun {σ : ℝ} (hσ : σ ∈ Icc 0 T) (j : Fin 2) (x : Pl) =>
    dConv_pd_all hν hC hb hb0 hA hAj hd hσ j x
  refine ⟨⟨dConv_cb0 hν hC hT hb hb0 hA, fun σ hσ x =>
    (dConv_deriv hν hC hb hb0 hA (hAj 0) (hAj 1) hd hσ x).differentiableAt, fun j => ?_⟩,
    fun σ hσ x => dConv_le hν hC hb hb0 hA hσ x, fun j => ?_⟩
  · exact CB0.congr (dConv_cb0 hν hC hT hb hb0 (hAj j)) fun σ hσ x => (hp hσ j x).symm
  · intro σ hσ x
    show |B0579.pd j (dConv ν A σ) x| ≤ _
    rw [hp hσ j x]
    exact dConv_le hν hC hb hb0 (hAj j) hσ x

/-- The class of a Duhamel integral with two derivatives. -/
theorem dConv_CB2 {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} {Aj : Fin 2 → ℝ → ℝ → Pl → ℝ}
    {Ajk : Fin 2 → Fin 2 → ℝ → ℝ → Pl → ℝ}
    (hν : 0 < ν) (hC : 0 ≤ C) (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T))
    (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A) (hAj : ∀ j, DAdm T C b (Aj j))
    (hAjk : ∀ i j, DAdm T C b (Ajk i j))
    (hd : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (A a r)
      (Aj 0 a r x • ContinuousLinearMap.fst ℝ ℝ ℝ + Aj 1 a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hd' : ∀ j : Fin 2, ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (Aj j a r)
      (Ajk 0 j a r x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Ajk 1 j a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) :
    CB T 2 (dConv ν A) ∧ CBle T 2 (dConv ν A) (Kconv (C * (1 + ν ^ (-(1 / 2 : ℝ)))) b) := by
  have hp := fun {σ : ℝ} (hσ : σ ∈ Icc 0 T) (j : Fin 2) (x : Pl) =>
    dConv_pd_all hν hC hb hb0 hA hAj hd hσ j x
  have h1 := fun j : Fin 2 => dConv_CB1 hν hC hT hb hb0 (hAj j) (fun i => hAjk i j) (hd' j)
  refine ⟨⟨dConv_cb0 hν hC hT hb hb0 hA, fun σ hσ x =>
    (dConv_deriv hν hC hb hb0 hA (hAj 0) (hAj 1) hd hσ x).differentiableAt, fun j => ?_⟩,
    fun σ hσ x => dConv_le hν hC hb hb0 hA hσ x, fun j => ?_⟩
  · exact CB.congr (h1 j).1 fun σ hσ x => (hp hσ j x).symm
  · exact CBle.congr (h1 j).2 fun σ hσ x => (hp hσ j x).symm

/-! ## Weighted bounds from the support in `η` -/

theorem wb_of {g : Pl → ℝ} {M R : ℝ} (hM : ∀ x, |g x| ≤ M) (hR : ∀ x : Pl, R < |x.2| → g x = 0) :
    WB (M * Real.cosh R) g := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  intro x
  by_cases hx : R < |x.2|
  · rw [hR x hx, abs_zero, zero_mul]
    exact mul_nonneg hM0 (Real.cosh_pos _).le
  · have h1 : Real.cosh x.2 ≤ Real.cosh R :=
      Real.cosh_le_cosh.2 ((not_lt.1 hx).trans (le_abs_self _))
    exact mul_le_mul (hM x) h1 (Real.cosh_pos _).le hM0

theorem heatSG_hasFDeriv {a M R : ℝ} (ha : 0 < a) {g : Pl → ℝ} (hgc : Continuous g)
    (hM : ∀ x, |g x| ≤ M) (hR : ∀ x : Pl, R < |x.2| → g x = 0) (x : Pl) :
    HasFDerivAt (heatSG a g) (heatSGd 0 a g x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      heatSGd 1 a g x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  obtain ⟨hd, hp, -⟩ := heatGradFormula _ g hgc (wb_of hM hR) a ha
  have h := (hd x).hasFDerivAt
  rw [fderiv_eq_pd, hp 0 x, hp 1 x] at h
  exact h

theorem cut_hasFDeriv {R : ℝ} {ψ : ℝ → ℝ} (hψ : IsCut R ψ) (x : Pl) :
    HasFDerivAt (fun y : Pl => ψ y.2) (dCut ψ 0 x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      dCut ψ 1 x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have h := ((hψ.differentiable.comp differentiable_snd) x).hasFDerivAt
  have e : (ψ ∘ Prod.snd : Pl → ℝ) = fun y : Pl => ψ y.2 := rfl
  rw [e, fderiv_eq_pd, pd_cut hψ.differentiable, pd_cut hψ.differentiable] at h
  exact h

/-! ## `GainZero`, `GainOne`, `GLinear` -/

/-- `G : C⁰_b → C¹_b`, with the derivative formula. -/
theorem gainZero_core {ν R : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) {F : ℝ → Pl → ℝ} {b : ℝ → ℝ}
    (hF : CB T 0 F) (hFs : EtaS T R F) (hb : ContinuousOn b (Icc 0 T))
    (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hFb : CBle T 0 F b) :
    CB T 1 (duhamelConv ν 0 F) ∧
      CBle T 1 (duhamelConv ν 0 F) (Kconv (9 * (1 + ν ^ (-(1 / 2 : ℝ)))) b) ∧
      ∀ σ ∈ Icc 0 T, ∀ (j : Fin 2) (x : Pl),
        B0579.pd j (duhamelConv ν 0 F σ) x = ∫ r in (0 : ℝ)..σ, heatSGd j (ν * (σ - r)) (F r) x := by
  have hA : DAdm T 9 b (fun a r x => heatSG a (F r) x) :=
    (admH hF hFb hb0).mono (by norm_num) hb0
  have hAj : ∀ j : Fin 2, DAdm T 9 b (fun a r x => heatSGd j a (F r) x) := fun j =>
    admHd j hF hFb hb0
  have hd : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt ((fun a r x => heatSG a (F r) x) a r)
      (heatSGd 0 a (F r) x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        heatSGd 1 a (F r) x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := fun a ha r hr x =>
    heatSG_hasFDeriv ha (DiffC.cont_slice hF.1 hr) (hFb r hr) (hFs r hr) x
  obtain ⟨h1, h2⟩ := dConv_CB1 (Aj := fun j a r x => heatSGd j a (F r) x) hν (by norm_num) hT hb hb0
    hA hAj hd
  exact ⟨h1, h2, fun σ hσ j x => dConv_pd_all (Aj := fun j a r x => heatSGd j a (F r) x) hν
    (by norm_num) hb hb0 hA hAj hd hσ j x⟩

/-- **Leaf `/4`.** -/
theorem gainZero : GainZero := by
  intro ν T R hν hT
  refine ⟨9 * (1 + ν ^ (-(1 / 2 : ℝ))), ?_, fun F b hF hFs hb hb0 hFb => ?_⟩
  · have := Real.rpow_nonneg hν.le (-(1 / 2 : ℝ))
    positivity
  · obtain ⟨h1, h2, -⟩ := gainZero_core hν hT hF hFs hb hb0 hFb
    exact ⟨h1, h2⟩

/-- **Leaf `/5`.** -/
theorem gainOne : GainOne := by
  intro ν T R hν hT
  refine ⟨9 * (1 + ν ^ (-(1 / 2 : ℝ))), ?_, fun F b hF hFs hb hb0 hFb => ?_⟩
  · have := Real.rpow_nonneg hν.le (-(1 / 2 : ℝ))
    positivity
  have hF0 : CB T 0 F := hF.1
  have hFb0 : CBle T 0 F b := hFb.1
  obtain ⟨h1, h2, hform⟩ := gainZero_core hν hT hF0 hFs hb hb0 hFb0
  have hd := fun j : Fin 2 =>
    gainZero_core hν hT (hF.2.2 j) (hFs.pd j) hb hb0 (hFb.2 j)
  obtain ⟨M, hM, hFM⟩ := CB.exists_le hF
  -- `∂_j G F = G ∂_j F`
  have hkey : ∀ σ ∈ Icc 0 T, ∀ (j : Fin 2) (x : Pl), B0579.pd j (duhamelConv ν 0 F σ) x =
      duhamelConv ν 0 (fun r => B0579.pd j (F r)) σ x := by
    intro σ hσ j x
    rw [hform σ hσ j x]
    unfold duhamelConv
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_pt σ] with r hne hr
    rw [uIoc_of_le hσ.1] at hr
    have hlt : r < σ := lt_of_le_of_ne hr.2 hne
    have hrI : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.trans hσ.2⟩
    have hC1 : ContDiff ℝ 1 (F r) := by
      have := CB.contDiff hF r hrI
      exact_mod_cast this
    exact heatSGd_eq_heatSG_pd heatGradFormula heatCommute (M * Real.cosh R) (F r) hC1
      (wb_of (hFM.1 r hrI) (hFs r hrI))
      (fun j => wb_of (CBle.top (hFM.2 j) r hrI) ((hFs.pd j) r hrI))
      _ (mul_pos hν (sub_pos.2 hlt)) j x
  refine ⟨⟨h1.1, h1.2.1, fun j => CB.congr (hd j).1 fun σ hσ x => (hkey σ hσ j x).symm⟩,
    ⟨h2.1, fun j => CBle.congr (hd j).2.1 fun σ hσ x => (hkey σ hσ j x).symm⟩, hkey⟩

/-- **Leaf `/3`.** -/
theorem gLinear : GLinear := by
  intro ν T R F F' c hν hT hF hF' hFs hF's σ hσ x
  obtain ⟨M, hM, hFM⟩ := CB.exists_le hF
  obtain ⟨M', hM', hFM'⟩ := CB.exists_le hF'
  have hA := admH (T := T) hF hFM (fun _ _ => hM)
  have hA' := admH (T := T) hF' hFM' (fun _ _ => hM')
  have hi := dConv_int hν zero_le_one continuousOn_const (fun _ _ => hM) hA hσ x
  have hi' := dConv_int hν zero_le_one continuousOn_const (fun _ _ => hM') hA' hσ x
  constructor
  · unfold duhamelConv
    rw [← intervalIntegral.integral_add hi hi']
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hσ.1] at hr
    have hrI : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hσ.2⟩
    simp only
    unfold heatSG
    split_ifs with ha
    · rfl
    · have ha' : 0 < ν * (σ - r) := not_le.1 ha
      rw [← integral_add (k_int ha' (DiffC.cont_slice hF.1 hrI) (hFM r hrI) x)
        (k_int ha' (DiffC.cont_slice hF'.1 hrI) (hFM' r hrI) x)]
      congr 1
      funext y
      ring
  · unfold duhamelConv
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only
    unfold heatSG
    split_ifs with ha
    · rfl
    · rw [← integral_const_mul]
      congr 1
      funext y
      ring

/-! ## `CommGain` -/

theorem hf_mul {f g : Pl → ℝ} {p0 p1 q0 q1 : ℝ} {x : Pl}
    (hf : HasFDerivAt f (p0 • ContinuousLinearMap.fst ℝ ℝ ℝ + p1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hg : HasFDerivAt g (q0 • ContinuousLinearMap.fst ℝ ℝ ℝ + q1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x) :
    HasFDerivAt (fun y => f y * g y) ((f x * q0 + g x * p0) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (f x * q1 + g x * p1) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  refine (hf.mul hg).congr_fderiv ?_
  ext <;> simp

theorem hf_add {f g : Pl → ℝ} {p0 p1 q0 q1 : ℝ} {x : Pl}
    (hf : HasFDerivAt f (p0 • ContinuousLinearMap.fst ℝ ℝ ℝ + p1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hg : HasFDerivAt g (q0 • ContinuousLinearMap.fst ℝ ℝ ℝ + q1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x) :
    HasFDerivAt (fun y => f y + g y) ((p0 + q0) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (p1 + q1) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  refine (hf.add hg).congr_fderiv ?_
  ext <;> simp

theorem hf_sub {f g : Pl → ℝ} {p0 p1 q0 q1 : ℝ} {x : Pl}
    (hf : HasFDerivAt f (p0 • ContinuousLinearMap.fst ℝ ℝ ℝ + p1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hg : HasFDerivAt g (q0 • ContinuousLinearMap.fst ℝ ℝ ℝ + q1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x) :
    HasFDerivAt (fun y => f y - g y) ((p0 - q0) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (p1 - q1) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  refine (hf.sub hg).congr_fderiv ?_
  ext <;> simp

theorem hf_congr {f : Pl → ℝ} {p0 p1 q0 q1 : ℝ} {x : Pl}
    (h : HasFDerivAt f (p0 • ContinuousLinearMap.fst ℝ ℝ ℝ + p1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (e0 : p0 = q0) (e1 : p1 = q1) :
    HasFDerivAt f (q0 • ContinuousLinearMap.fst ℝ ℝ ℝ + q1 • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  subst e0 e1
  exact h

/-- Lipschitz bound of a cutoff. -/
theorem IsCut.lipschitz {R : ℝ} {ψ : ℝ → ℝ} (hψ : IsCut R ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t, |ψ s - ψ t| ≤ L * |s - t| := by
  obtain ⟨C, hC⟩ := hψ.deriv.exists_bound
  refine ⟨|C|, abs_nonneg _, fun s t => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ψ) (C := |C|) (s := univ) (x := t)
    (y := s) (fun x _ => hψ.differentiable x)
    (fun x _ => by
      rw [Real.norm_eq_abs]
      exact (hC x).trans (le_abs_self _)) convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using h

theorem IsCut.dCut_bound {R : ℝ} {ψ : ℝ → ℝ} (hψ : IsCut R ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) (t : ℝ), |LS.dCut ψ j t| ≤ C := by
  obtain ⟨C0, h0⟩ := (hψ.dCut 0).exists_bound
  obtain ⟨C1, h1⟩ := (hψ.dCut 1).exists_bound
  refine ⟨|C0| + |C1|, by positivity, fun j t => ?_⟩
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · exact (h0 t).trans ((le_abs_self _).trans (by linarith [abs_nonneg C1]))
  · exact (h1 t).trans ((le_abs_self _).trans (by linarith [abs_nonneg C0]))

set_option maxHeartbeats 1000000 in
/-- **Leaf `/6`: the commutator gains two derivatives.** -/
theorem commGain : CommGain := by
  intro ν T R R' ψ hν hT hψ
  obtain ⟨Cψ0, hCψ0⟩ := hψ.exists_bound
  set Cψ := |Cψ0| with hCψdef
  have hCψ : ∀ t, |ψ t| ≤ Cψ := fun t => (hCψ0 t).trans (le_abs_self _)
  have hCψn : 0 ≤ Cψ := abs_nonneg _
  obtain ⟨C1, hC1n, hC1⟩ := hψ.dCut_bound
  obtain ⟨C20, hC20n, hC20⟩ := (hψ.dCut 0).dCut_bound
  obtain ⟨C21, hC21n, hC21⟩ := (hψ.dCut 1).dCut_bound
  set C2 := C20 + C21 with hC2def
  have hC2n : 0 ≤ C2 := by positivity
  have hC2 : ∀ (i j : Fin 2) (t : ℝ), |dCut (dCut ψ j) i t| ≤ C2 := by
    intro i j t
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj with rfl | rfl
    · exact (hC20 i t).trans (by linarith)
    · exact (hC21 i t).trans (by linarith)
  obtain ⟨L, hLn, hL⟩ := hψ.lipschitz
  set Cc : ℝ := 2 * Cψ + (C1 + 18 * Cψ) + (C2 + 18 * C1 + 77 * L) with hCcdef
  have hCcn : 0 ≤ Cc := by positivity
  refine ⟨Cc * (1 + ν ^ (-(1 / 2 : ℝ))), ?_, fun F b hF hFs hb hb0 hFb => ?_⟩
  · have := Real.rpow_nonneg hν.le (-(1 / 2 : ℝ))
    positivity
  have hψc := hψ.continuous
  have hψF : CB0 T (mulC ψ F) := CB.mulC hψ hF
  have hψFb : CBle T 0 (mulC ψ F) (fun r => Cψ * b r) := fun r hr x => by
    show |ψ x.2 * F r x| ≤ Cψ * b r
    rw [abs_mul]
    exact mul_le_mul (hCψ _) (hFb r hr x) (abs_nonneg _) hCψn
  have hψFb0 : ∀ r ∈ Icc 0 T, 0 ≤ Cψ * b r := fun r hr => mul_nonneg hCψn (hb0 r hr)
  have hψFs : EtaS T R (mulC ψ F) := EtaS.mul_left _ hFs
  have hsl : ∀ r ∈ Icc 0 T, Continuous (F r) := fun r hr => DiffC.cont_slice hF.1 hr
  have hslψ : ∀ r ∈ Icc 0 T, Continuous (mulC ψ F r) := fun r hr => DiffC.cont_slice hψF.1 hr
  -- the integrands
  let A : ℝ → ℝ → Pl → ℝ := fun a r x => ψ x.2 * heatSG a (F r) x - heatSG a (mulC ψ F r) x
  let Aj : Fin 2 → ℝ → ℝ → Pl → ℝ := fun j a r x =>
    dCut ψ j x.2 * heatSG a (F r) x + ψ x.2 * heatSGd j a (F r) x - heatSGd j a (mulC ψ F r) x
  let Ajk : Fin 2 → Fin 2 → ℝ → ℝ → Pl → ℝ := fun i j a r x =>
    dCut (dCut ψ j) i x.2 * heatSG a (F r) x + dCut ψ j x.2 * heatSGd i a (F r) x +
      (dCut ψ i x.2 * heatSGd j a (F r) x + ψ x.2 * heatSGdd i j a (F r) x) -
        heatSGdd i j a (mulC ψ F r) x
  have hcutcont : ∀ (φ : ℝ → ℝ), Continuous φ →
      ContinuousOn (fun p : ℝ × ℝ × Pl => φ p.2.2.2) (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) := fun φ h =>
    (h.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousOn
  -- sizes
  have hkap : ∀ {a : ℝ}, 0 < a → ∀ r ∈ Icc 0 T,
      0 ≤ (1 + a ^ (-(1 / 2 : ℝ))) * b r ∧ b r ≤ (1 + a ^ (-(1 / 2 : ℝ))) * b r ∧
        (Real.sqrt a)⁻¹ * b r ≤ (1 + a ^ (-(1 / 2 : ℝ))) * b r := by
    intro a ha r hr
    have h1 := one_le_kernel ha
    have h2 := sqrt_inv_le_kernel ha
    have h3 := hb0 r hr
    refine ⟨by nlinarith, by nlinarith, mul_le_mul_of_nonneg_right h2 h3⟩
  have hA : DAdm T Cc b A := by
    refine ⟨((hcutcont ψ hψc).mul (heatSG_joint hF)).sub (heatSG_joint hψF), fun a ha r hr x => ?_⟩
    obtain ⟨k0, k1, k2⟩ := hkap ha r hr
    have h1 := heatSG_abs_le ha (hFb r hr) x
    have h2 := heatSG_abs_le ha (hψFb r hr) x
    have h3 : |ψ x.2 * heatSG a (F r) x| ≤ Cψ * b r := by
      rw [abs_mul]
      exact mul_le_mul (hCψ _) h1 (abs_nonneg _) hCψn
    have h4 := abs_sub (ψ x.2 * heatSG a (F r) x) (heatSG a (mulC ψ F r) x)
    calc |ψ x.2 * heatSG a (F r) x - heatSG a (mulC ψ F r) x| ≤ 2 * Cψ * b r := by linarith
      _ ≤ 2 * Cψ * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) :=
          mul_le_mul_of_nonneg_left k1 (by positivity)
      _ ≤ Cc * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) := by
          refine mul_le_mul_of_nonneg_right ?_ k0
          rw [hCcdef]
          nlinarith
      _ = _ := by ring
  have hAj : ∀ j, DAdm T Cc b (Aj j) := by
    intro j
    refine ⟨(((hcutcont _ (hψ.dCut j).continuous).mul (heatSG_joint hF)).add
      ((hcutcont ψ hψc).mul (heatSGd_joint j hF))).sub (heatSGd_joint j hψF),
      fun a ha r hr x => ?_⟩
    obtain ⟨k0, k1, k2⟩ := hkap ha r hr
    have h1 := heatSG_abs_le ha (hFb r hr) x
    have h2 := heatSGd_abs_le ha j (hFb r hr) x
    have h3 := heatSGd_abs_le ha j (hψFb r hr) x
    have h4 : |dCut ψ j x.2 * heatSG a (F r) x| ≤ C1 * b r := by
      rw [abs_mul]
      exact mul_le_mul (hC1 _ _) h1 (abs_nonneg _) hC1n
    have h5 : |ψ x.2 * heatSGd j a (F r) x| ≤ Cψ * (9 * (Real.sqrt a)⁻¹ * b r) := by
      rw [abs_mul]
      exact mul_le_mul (hCψ _) h2 (abs_nonneg _) hCψn
    have h6 : |dCut ψ j x.2 * heatSG a (F r) x + ψ x.2 * heatSGd j a (F r) x -
        heatSGd j a (mulC ψ F r) x| ≤ C1 * b r + 18 * Cψ * ((Real.sqrt a)⁻¹ * b r) := by
      refine (abs_sub _ _).trans ?_
      have := abs_add_le (dCut ψ j x.2 * heatSG a (F r) x) (ψ x.2 * heatSGd j a (F r) x)
      nlinarith
    refine h6.trans ?_
    have e1 : C1 * b r ≤ C1 * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) :=
      mul_le_mul_of_nonneg_left k1 hC1n
    have e2 : 18 * Cψ * ((Real.sqrt a)⁻¹ * b r) ≤ 18 * Cψ * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) :=
      mul_le_mul_of_nonneg_left k2 (by positivity)
    have e3 : (C1 + 18 * Cψ) * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) ≤
        Cc * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) := by
      refine mul_le_mul_of_nonneg_right ?_ k0
      rw [hCcdef]
      nlinarith
    nlinarith
  have hAjk : ∀ i j, DAdm T Cc b (Ajk i j) := by
    intro i j
    have c1 := (hcutcont _ ((hψ.dCut j).dCut i).continuous).mul (heatSG_joint hF)
    have c2 := (hcutcont _ (hψ.dCut j).continuous).mul (heatSGd_joint i hF)
    have c3 := (hcutcont _ (hψ.dCut i).continuous).mul (heatSGd_joint j hF)
    have c4 := (hcutcont ψ hψc).mul (heatSGdd_joint i j hF)
    refine ⟨((c1.add c2).add (c3.add c4)).sub (heatSGdd_joint i j hψF), fun a ha r hr x => ?_⟩
    obtain ⟨k0, k1, k2⟩ := hkap ha r hr
    have h1 := heatSG_abs_le ha (hFb r hr) x
    have h2 := heatSGd_abs_le ha i (hFb r hr) x
    have h3 := heatSGd_abs_le ha j (hFb r hr) x
    have hcomm := comm_dd_le ha hLn hL hψc hCψ (hsl r hr) (hFb r hr) i j x
    have h4 : |dCut (dCut ψ j) i x.2 * heatSG a (F r) x| ≤ C2 * b r := by
      rw [abs_mul]
      exact mul_le_mul (hC2 _ _ _) h1 (abs_nonneg _) hC2n
    have h5 : |dCut ψ j x.2 * heatSGd i a (F r) x| ≤ C1 * (9 * (Real.sqrt a)⁻¹ * b r) := by
      rw [abs_mul]
      exact mul_le_mul (hC1 _ _) h2 (abs_nonneg _) hC1n
    have h6 : |dCut ψ i x.2 * heatSGd j a (F r) x| ≤ C1 * (9 * (Real.sqrt a)⁻¹ * b r) := by
      rw [abs_mul]
      exact mul_le_mul (hC1 _ _) h3 (abs_nonneg _) hC1n
    have h7 : |Ajk i j a r x| ≤ C2 * b r + (18 * C1 + 77 * L) * ((Real.sqrt a)⁻¹ * b r) := by
      have e : Ajk i j a r x = dCut (dCut ψ j) i x.2 * heatSG a (F r) x +
          dCut ψ j x.2 * heatSGd i a (F r) x + dCut ψ i x.2 * heatSGd j a (F r) x +
          (ψ x.2 * heatSGdd i j a (F r) x - heatSGdd i j a (fun y => ψ y.2 * F r y) x) := by
        have e' : mulC ψ F r = fun y => ψ y.2 * F r y := rfl
        simp only [Ajk]
        rw [e']
        ring
      rw [e]
      have t1 := abs_add_le (dCut (dCut ψ j) i x.2 * heatSG a (F r) x +
          dCut ψ j x.2 * heatSGd i a (F r) x + dCut ψ i x.2 * heatSGd j a (F r) x)
          (ψ x.2 * heatSGdd i j a (F r) x - heatSGdd i j a (fun y => ψ y.2 * F r y) x)
      have t2 := abs_add_le (dCut (dCut ψ j) i x.2 * heatSG a (F r) x +
          dCut ψ j x.2 * heatSGd i a (F r) x) (dCut ψ i x.2 * heatSGd j a (F r) x)
      have t3 := abs_add_le (dCut (dCut ψ j) i x.2 * heatSG a (F r) x)
          (dCut ψ j x.2 * heatSGd i a (F r) x)
      nlinarith
    refine h7.trans ?_
    have e1 : C2 * b r ≤ C2 * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) :=
      mul_le_mul_of_nonneg_left k1 hC2n
    have e2 : (18 * C1 + 77 * L) * ((Real.sqrt a)⁻¹ * b r) ≤
        (18 * C1 + 77 * L) * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) :=
      mul_le_mul_of_nonneg_left k2 (by positivity)
    have e3 : (C2 + (18 * C1 + 77 * L)) * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) ≤
        Cc * ((1 + a ^ (-(1 / 2 : ℝ))) * b r) := by
      refine mul_le_mul_of_nonneg_right ?_ k0
      rw [hCcdef]
      nlinarith
    nlinarith
  -- derivatives
  have hfst : ∀ (p q : ℝ), (p • ContinuousLinearMap.fst ℝ ℝ ℝ + q • ContinuousLinearMap.snd ℝ ℝ ℝ :
      Pl →L[ℝ] ℝ) ((1 : ℝ), (0 : ℝ)) = p := fun p q => by simp
  have hd : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (A a r)
      (Aj 0 a r x • ContinuousLinearMap.fst ℝ ℝ ℝ + Aj 1 a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    intro a ha r hr x
    have h1 := cut_hasFDeriv hψ x
    have h2 := heatSG_hasFDeriv ha (hsl r hr) (hFb r hr) (hFs r hr) x
    have h3 := heatSG_hasFDeriv ha (hslψ r hr) (hψFb r hr) (hψFs r hr) x
    refine hf_congr (hf_sub (hf_mul h1 h2) h3) ?_ ?_ <;> simp only [Aj] <;> ring
  have hd' : ∀ j : Fin 2, ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (Aj j a r)
      (Ajk 0 j a r x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Ajk 1 j a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    intro j a ha r hr x
    have h1 := cut_hasFDeriv (hψ.dCut j) x
    have h2 := heatSG_hasFDeriv ha (hsl r hr) (hFb r hr) (hFs r hr) x
    have h3 := cut_hasFDeriv hψ x
    have h4 := heatSGd_hasFDeriv ha j (hsl r hr) (hFb r hr) x
    have h5 := heatSGd_hasFDeriv ha j (hslψ r hr) (hψFb r hr) x
    refine hf_congr (hf_sub (hf_add (hf_mul h1 h2) (hf_mul h3 h4)) h5) ?_ ?_ <;>
      simp only [Ajk] <;> ring
  obtain ⟨g1, g2⟩ := dConv_CB2 hν hCcn hT hb hb0 hA hAj hAjk hd hd'
  -- the identification with the commutator
  have hidc : ∀ σ ∈ Icc 0 T, ∀ x : Pl, dConv ν A σ x = comm ν ψ F σ x := by
    intro σ hσ x
    have hi1 := dConv_int hν zero_le_one hb hb0 (admH hF hFb hb0) hσ x
    have hi2 := dConv_int hν zero_le_one (continuousOn_const.mul hb) hψFb0
      (admH hψF hψFb hψFb0) hσ x
    unfold dConv comm duhamelConv
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hi1.const_mul _) hi2]
  exact ⟨CB.congr g1 hidc, CBle.congr g2 hidc⟩

/-! ## `TruncDrift`, `FreeCB` -/

/-- **Leaf `/1`.** -/
theorem truncDrift : TruncDrift := by
  intro c T R U θ hc hU hper hθ m
  have hzero : ∀ {U : ℝ → Pl → ℝ} {θ : ℝ → ℝ},
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => U z.1 z.2) (Icc 0 T ×ˢ univ) →
      (∀ σ ∈ Icc 0 T, ∀ x : Pl, U σ (x.1 + c, x.2) = U σ x) → IsCut R θ → CB0 T (mulC θ U) := by
    intro U θ hU hper hθ
    obtain ⟨Cθ, hCθ⟩ := hθ.exists_bound
    obtain ⟨M, hM⟩ := bandBounded c 0 T (-|R|) |R| U hc hU.continuousOn hper
    refine ⟨((hθ.continuous.comp (continuous_snd.comp continuous_snd)).continuousOn).mul
      hU.continuousOn, Cθ * |M|, fun σ hσ x => ?_⟩
    have hCθ0 : 0 ≤ Cθ := (abs_nonneg _).trans (hCθ 0)
    show |θ x.2 * U σ x| ≤ Cθ * |M|
    by_cases hx : R < |x.2|
    · rw [hθ.supp _ hx, zero_mul, abs_zero]
      positivity
    · rw [abs_mul]
      have hmem : x.2 ∈ Icc (-|R|) |R| := abs_le.1 ((not_lt.1 hx).trans (le_abs_self _))
      exact mul_le_mul (hCθ _) ((hM σ hσ x hmem).trans (le_abs_self _)) (abs_nonneg _) hCθ0
  induction m generalizing U θ with
  | zero => exact hzero hU hper hθ
  | succ m ih =>
      have hsl : ∀ σ ∈ Icc 0 T, Differentiable ℝ (U σ) := by
        intro σ hσ
        have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Pl => (σ, x)) univ :=
          (contDiff_const.prodMk contDiff_id).contDiffOn
        have h := hU.comp hcomp (fun x _ => ⟨hσ, mem_univ _⟩)
        exact (contDiffOn_univ.1 h).differentiable (by simp)
      refine ⟨hzero hU hper hθ, fun σ hσ =>
        (hθ.differentiable.comp differentiable_snd).mul (hsl σ hσ), fun j => ?_⟩
      have h1 := ih (fun σ => B0579.pd j (U σ)) θ (pdJointSmooth 0 T U j hU)
        (fun σ hσ x => pdPeriodic c (U σ) j (hper σ hσ) x) hθ
      have h2 := ih U (dCut θ j) hU hper (hθ.dCut j)
      refine CB.congr (CB.add h1 h2) fun σ hσ x => ?_
      show θ x.2 * B0579.pd j (U σ) x + dCut θ j x.2 * U σ x = B0579.pd j (fun y => θ y.2 * U σ y) x
      rw [pd_mulC hθ.differentiable (hsl σ hσ x) j]
      ring

/-- **Leaf `/2`.** -/
theorem freeCB : FreeCB := by
  intro c ν T f hc hν hT hf m
  have hbd : ∀ {f : Pl → ℝ}, B0579.IsCylTest c f → ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := cylTestBounded c f hc hf
    exact ⟨|M|, abs_nonneg _, fun x => (hM x).trans (le_abs_self _)⟩
  have hzero : ∀ {f : Pl → ℝ}, B0579.IsCylTest c f → CB0 T (fun σ => heatSG (ν * σ) f) := by
    intro f hf
    obtain ⟨M, hM0, hM⟩ := hbd hf
    obtain ⟨R, hR⟩ := hf.band
    have hW := wb_of hM hR
    have hcont := heatCont _ f hf.continuous hW
    have hmap : ContinuousOn (fun z : ℝ × Pl => ((ν * z.1, z.2) : ℝ × Pl)) (Icc 0 T ×ˢ univ) := by
      apply Continuous.continuousOn
      fun_prop
    refine ⟨hcont.comp hmap fun z hz => ⟨mul_nonneg hν.le hz.1.1, mem_univ _⟩, M, fun σ hσ x => ?_⟩
    rcases hσ.1.eq_or_lt with h0 | h0
    · show |heatSG (ν * σ) f x| ≤ M
      rw [← h0, mul_zero]
      simpa [heatSG] using hM x
    · exact heatSG_abs_le (mul_pos hν h0) hM x
  induction m generalizing f with
  | zero => exact hzero hf
  | succ m ih =>
      obtain ⟨M, hM0, hM⟩ := hbd hf
      obtain ⟨R, hR⟩ := hf.band
      obtain ⟨M0, hM00, hM0'⟩ := hbd (hf.pd 0)
      obtain ⟨M1, hM10, hM1'⟩ := hbd (hf.pd 1)
      obtain ⟨R0, hR0⟩ := (hf.pd 0).band
      obtain ⟨R1, hR1⟩ := (hf.pd 1).band
      refine ⟨hzero hf, fun σ hσ => ?_, fun j => ?_⟩
      · rcases hσ.1.eq_or_lt with h0 | h0
        · have e : heatSG (ν * σ) f = f := by
            funext x
            rw [← h0, mul_zero]
            simp [heatSG]
          show Differentiable ℝ (heatSG (ν * σ) f)
          rw [e]
          exact hf.differentiable
        · exact (heatGradFormula _ f hf.continuous (wb_of hM hR) _ (mul_pos hν h0)).1
      · -- a common weight for `f` and `∂_j f`
        set Rm := max R (max R0 R1) with hRm
        set Mm := M + M0 + M1 with hMm
        have hle1 : ∀ x, |f x| ≤ Mm := fun x => (hM x).trans (by linarith)
        have hl0 : ∀ x : Pl, Rm < |x.2| → f x = 0 := fun x hx =>
          hR x (lt_of_le_of_lt (le_max_left _ _) hx)
        have hWf := wb_of hle1 hl0
        have hWd : ∀ j : Fin 2, WB (Mm * Real.cosh Rm) (B0579.pd j f) := by
          intro j
          have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
          rcases hj with rfl | rfl
          · exact wb_of (fun x => (hM0' x).trans (by linarith)) fun x hx =>
              hR0 x (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hx)
          · exact wb_of (fun x => (hM1' x).trans (by linarith)) fun x hx =>
              hR1 x (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hx)
        have hC1 : ContDiff ℝ 1 f := hf.smooth.of_le (by simp)
        refine CB.congr (ih _ (hf.pd j)) fun σ _ x => ?_
        exact (heatCommute _ f hC1 hWf hWd (ν * σ) j x).symm

end LS

end UnforcedLeray.Short.IIb.BwdRoute
