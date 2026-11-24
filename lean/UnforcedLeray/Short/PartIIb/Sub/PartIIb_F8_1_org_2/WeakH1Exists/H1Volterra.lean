import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.WeakH1Exists.ShiftAvg
import UnforcedLeray.Infra.VolterraEvolution.StripLaw
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Solenoidal `H¹` Volterra mild/weak evolution for `PartII-b:F8/1/org/2/1`

Constructs the closed Banach subspace `H1Sol c ⊆ L2v c × L2v c × L2v c` of solenoidal `H¹_σ(C_c)`
triples `(w, ∂_q w, ∂_η w)`, instantiates `VolterraEvolution.VolterraData` on `X = H1Sol c`,
`Y = L2v c` at normalized time `τ = t / 2 ∈ [0, 1]` (so every subinterval `[a, t] ⊆ [0, 2]` lies
inside a single unit strip), and proves `RealCylOseenWeakH1Exists`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.F8WeakEx

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder
open UnforcedLeray.Infra.VolterraEvolution

private abbrev Coord := ℝ × Plane

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private lemma clm_intervalIntegrable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => L (f x)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

/-! ## 1. Solenoidal `H¹_σ(C_c)` Banach space `H1Sol c` -/

abbrev TripleL2 (c : ℝ) : Type := L2v c × L2v c × L2v c

lemma centeredHeatVecL2CLM_P0_comm {c : ℝ} (hc : 0 < c) (θ : ℝ) (x : L2v c) :
    centeredHeatVecL2CLM hc θ (P0 c x) = P0 c (centeredHeatVecL2CLM hc θ x) := by
  by_cases hθ : 0 < θ
  · rw [centeredHeat_eq_shiftAvgCLM hc hθ, centeredHeat_eq_shiftAvgCLM hc hθ]
    exact shiftAvgCLM_P0_comm hc _ x
  · simp [centeredHeatVecL2CLM_eq_id_of_nonpos hc (not_lt.mp hθ)]

lemma hasWeakCellDerivR_l2_iff {c : ℝ} (x dx : L2v c) (j : Fin 2) :
    (∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) ↔
      ∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        ⟪x, cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k)⟫_ℝ +
          ⟪dx, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0 := by
  constructor
  · intro h ψ hψ k
    rw [inner_cylSmooth_single (hψ.pd j) k x, inner_cylSmooth_single hψ k dx, (h k).2 ψ hψ]
    ring
  · intro h k
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hmψ : MemLp ψ 2 (cellμ c) := memLp_cellμ_of_test hψ
      have hmpd : MemLp (B0579.pd j ψ) 2 (cellμ c) := memLp_cellμ_of_test (hψ.pd j)
      rw [b0579_cell_eq_cyl_cell]
      exact ⟨(UnforcedLeray.Cyl.memLp_component x k).integrable_mul hmpd,
        (UnforcedLeray.Cyl.memLp_component dx k).integrable_mul hmψ⟩
    · have hk := h ψ hψ k
      rw [inner_cylSmooth_single (hψ.pd j) k x, inner_cylSmooth_single hψ k dx] at hk
      linarith

def H1Sol (c : ℝ) : Submodule ℝ (TripleL2 c) where
  carrier := {p | p.1 ∈ divFree c ∧
    (∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
      ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 0) k)⟫_ℝ +
        ⟪p.2.1, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0) ∧
    (∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
      ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 1) k)⟫_ℝ +
        ⟪p.2.2, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0)}
  zero_mem' := ⟨(divFree c).zero_mem, fun _ _ _ => by simp, fun _ _ _ => by simp⟩
  add_mem' {p q} hp hq := ⟨(divFree c).add_mem hp.1 hq.1,
    fun ψ hψ k => by
      simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
      linarith [hp.2.1 ψ hψ k, hq.2.1 ψ hψ k],
    fun ψ hψ k => by
      simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
      linarith [hp.2.2 ψ hψ k, hq.2.2 ψ hψ k]⟩
  smul_mem' r {p} hp := ⟨(divFree c).smul_mem r hp.1,
    fun ψ hψ k => by
      simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, RCLike.conj_to_real]
      linear_combination r * hp.2.1 ψ hψ k,
    fun ψ hψ k => by
      simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, RCLike.conj_to_real]
      linear_combination r * hp.2.2 ψ hψ k⟩

lemma isClosed_H1Sol (c : ℝ) : IsClosed (H1Sol c : Set (TripleL2 c)) := by
  have heq : (H1Sol c : Set (TripleL2 c)) =
      (Prod.fst ⁻¹' (divFree c : Set (L2v c))) ∩
      ((⋂ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        {p : TripleL2 c |
          ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 0) k)⟫_ℝ +
            ⟪p.2.1, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0}) ∩
       (⋂ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        {p : TripleL2 c |
          ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 1) k)⟫_ℝ +
            ⟪p.2.2, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0})) := by
    ext p
    simp [H1Sol]
  rw [heq]
  refine ((UnforcedLeray.Cyl.isClosed_divFree c).preimage continuous_fst).inter (IsClosed.inter ?_ ?_)
  · refine isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun k => ?_
    exact isClosed_eq
      ((continuous_fst.inner continuous_const).add
        ((continuous_fst.comp continuous_snd).inner continuous_const))
      continuous_const
  · refine isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun k => ?_
    exact isClosed_eq
      ((continuous_fst.inner continuous_const).add
        ((continuous_snd.comp continuous_snd).inner continuous_const))
      continuous_const

instance completeSpace_H1Sol (c : ℝ) : CompleteSpace (H1Sol c) :=
  (isClosed_H1Sol c).completeSpace_coe

def val0CLM (c : ℝ) : H1Sol c →L[ℝ] L2v c :=
  (ContinuousLinearMap.fst ℝ (L2v c) (L2v c × L2v c)).comp (H1Sol c).subtypeL

def dqCLM (c : ℝ) : H1Sol c →L[ℝ] L2v c :=
  ((ContinuousLinearMap.fst ℝ (L2v c) (L2v c)).comp
    (ContinuousLinearMap.snd ℝ (L2v c) (L2v c × L2v c))).comp (H1Sol c).subtypeL

def detaCLM (c : ℝ) : H1Sol c →L[ℝ] L2v c :=
  ((ContinuousLinearMap.snd ℝ (L2v c) (L2v c)).comp
    (ContinuousLinearMap.snd ℝ (L2v c) (L2v c × L2v c))).comp (H1Sol c).subtypeL

@[simp] lemma val0CLM_apply {c : ℝ} (p : H1Sol c) : val0CLM c p = p.1.1 := rfl
@[simp] lemma dqCLM_apply {c : ℝ} (p : H1Sol c) : dqCLM c p = p.1.2.1 := rfl
@[simp] lemma detaCLM_apply {c : ℝ} (p : H1Sol c) : detaCLM c p = p.1.2.2 := rfl

lemma norm_val0CLM_le {c : ℝ} (p : H1Sol c) : ‖val0CLM c p‖ ≤ ‖p‖ :=
  norm_fst_le p.1

lemma norm_dqCLM_le {c : ℝ} (p : H1Sol c) : ‖dqCLM c p‖ ≤ ‖p‖ :=
  (norm_fst_le p.1.2).trans (norm_snd_le p.1)

lemma norm_detaCLM_le {c : ℝ} (p : H1Sol c) : ‖detaCLM c p‖ ≤ ‖p‖ :=
  (norm_snd_le p.1.2).trans (norm_snd_le p.1)

lemma H1Sol.mem_divFree {c : ℝ} (p : H1Sol c) : val0CLM c p ∈ divFree c := p.2.1

lemma H1Sol.weak_q {c : ℝ} (p : H1Sol c) :
    ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c 0
      (fun y => (val0CLM c p : Plane → F8Ex.RMerid) y k)
      (fun y => (dqCLM c p : Plane → F8Ex.RMerid) y k) :=
  (hasWeakCellDerivR_l2_iff (val0CLM c p) (dqCLM c p) 0).2 p.2.2.1

lemma H1Sol.weak_eta {c : ℝ} (p : H1Sol c) :
    ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c 1
      (fun y => (val0CLM c p : Plane → F8Ex.RMerid) y k)
      (fun y => (detaCLM c p : Plane → F8Ex.RMerid) y k) :=
  (hasWeakCellDerivR_l2_iff (val0CLM c p) (detaCLM c p) 1).2 p.2.2.2

def H1Sol.mkOfWeak {c : ℝ} (u uq uη : L2v c) (hdiv : u ∈ divFree c)
    (hq : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c 0 (fun y => u y k) (fun y => uq y k))
    (hη : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c 1 (fun y => u y k) (fun y => uη y k)) :
    H1Sol c :=
  ⟨(u, uq, uη), hdiv, (hasWeakCellDerivR_l2_iff u uq 0).1 hq,
    (hasWeakCellDerivR_l2_iff u uη 1).1 hη⟩

lemma H1Sol.ext_val0 {c : ℝ} (hc : 0 < c) {p q : H1Sol c}
    (h : val0CLM c p = val0CLM c q) : p = q := by
  apply Subtype.ext
  refine Prod.ext h (Prod.ext ?_ ?_)
  · refine eq_of_hasWeakCellDerivR hc (H1Sol.weak_q p) (fun k => ?_)
    have hqk := H1Sol.weak_q q k
    rwa [← h] at hqk
  · refine eq_of_hasWeakCellDerivR hc (H1Sol.weak_eta p) (fun k => ?_)
    have hηk := H1Sol.weak_eta q k
    rwa [← h] at hηk

lemma hasWeakCellDerivR_congr_ae {c : ℝ} {j : Fin 2} {φ₁ φ₂ g₁ g₂ : Plane → ℝ}
    (hφ : φ₁ =ᵐ[F8Ex.cellMeas c] φ₂) (hg : g₁ =ᵐ[F8Ex.cellMeas c] g₂)
    (h1 : F8Ex.HasWeakCellDerivR c j φ₁ g₁) :
    F8Ex.HasWeakCellDerivR c j φ₂ g₂ := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨i1, i2⟩ := h1.1 ψ hψ
    refine ⟨i1.congr ?_, i2.congr ?_⟩
    · filter_upwards [hφ] with y hy; rw [hy]
    · filter_upwards [hg] with y hy; rw [hy]
  · have e1 : ∫ y in B0579.cell c, φ₂ y * B0579.pd j ψ y =
        ∫ y in B0579.cell c, φ₁ y * B0579.pd j ψ y := by
      refine integral_congr_ae ?_
      filter_upwards [hφ] with y hy; rw [hy]
    have e2 : ∫ y in B0579.cell c, g₂ y * ψ y = ∫ y in B0579.cell c, g₁ y * ψ y := by
      refine integral_congr_ae ?_
      filter_upwards [hg] with y hy; rw [hy]
    rw [e1, e2, h1.2 ψ hψ]

lemma isRealCellSolenoidal_congr_ae {c : ℝ} {f₁ f₂ : Plane → F8Ex.RMerid}
    (hf : f₁ =ᵐ[F8Ex.cellMeas c] f₂) (h1 : F8Ex.IsRealCellSolenoidal c f₁) :
    F8Ex.IsRealCellSolenoidal c f₂ := by
  intro ψ hψ
  obtain ⟨hi, hz⟩ := h1 ψ hψ
  have hae : (fun y => f₁ y 0 * B0579.pd 0 ψ y + f₁ y 1 * B0579.pd 1 ψ y) =ᵐ[F8Ex.cellMeas c]
      fun y => f₂ y 0 * B0579.pd 0 ψ y + f₂ y 1 * B0579.pd 1 ψ y := by
    filter_upwards [hf] with y hy; rw [hy]
  exact ⟨hi.congr hae, (integral_congr_ae hae.symm).trans hz⟩

private lemma ae_cellMeas_of_ae_cellμ {c : ℝ} {P : Plane → Prop}
    (h : ∀ᵐ y ∂(cellμ c), P y) : ∀ᵐ y ∂(F8Ex.cellMeas c), P y := by
  rwa [cellMeas_eq_cellμ]

def H1Sol.ofRealDatum {c : ℝ} {u uq uη : Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη) : H1Sol c := by
  have hm0 : MemLp u 2 (cellμ c) := by rw [← cellMeas_eq_cellμ]; exact hdat.memL2.1
  have hmq : MemLp uq 2 (cellμ c) := by rw [← cellMeas_eq_cellμ]; exact hdat.memL2.2.1
  have hmη : MemLp uη 2 (cellμ c) := by rw [← cellMeas_eq_cellμ]; exact hdat.memL2.2.2
  let uL := hm0.toLp u
  let uqL := hmq.toLp uq
  let uηL := hmη.toLp uη
  have hae0 : u =ᵐ[F8Ex.cellMeas c] (uL : Plane → F8Ex.RMerid) :=
    ae_cellMeas_of_ae_cellμ hm0.coeFn_toLp.symm
  have haeq : uq =ᵐ[F8Ex.cellMeas c] (uqL : Plane → F8Ex.RMerid) :=
    ae_cellMeas_of_ae_cellμ hmq.coeFn_toLp.symm
  have haeη : uη =ᵐ[F8Ex.cellMeas c] (uηL : Plane → F8Ex.RMerid) :=
    ae_cellMeas_of_ae_cellμ hmη.coeFn_toLp.symm
  refine H1Sol.mkOfWeak uL uqL uηL ?_ ?_ ?_
  · rw [mem_divFree_iff_solenoidal]
    exact isRealCellSolenoidal_congr_ae hae0 hdat.solenoidal
  · intro k
    exact hasWeakCellDerivR_congr_ae
      (hae0.mono fun y hy => congrArg (fun v : F8Ex.RMerid => v k) hy)
      (haeq.mono fun y hy => congrArg (fun v : F8Ex.RMerid => v k) hy)
      (hdat.weak_q k)
  · intro k
    exact hasWeakCellDerivR_congr_ae
      (hae0.mono fun y hy => congrArg (fun v : F8Ex.RMerid => v k) hy)
      (haeη.mono fun y hy => congrArg (fun v : F8Ex.RMerid => v k) hy)
      (hdat.weak_eta k)

lemma H1Sol.ofRealDatum_ae {c : ℝ} {u uq uη : Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη) :
    ((val0CLM c (H1Sol.ofRealDatum hdat) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] u) ∧
    ((dqCLM c (H1Sol.ofRealDatum hdat) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] uq) ∧
    ((detaCLM c (H1Sol.ofRealDatum hdat) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] uη) := by
  have hm0 : MemLp u 2 (cellμ c) := by rw [← cellMeas_eq_cellμ]; exact hdat.memL2.1
  have hmq : MemLp uq 2 (cellμ c) := by rw [← cellMeas_eq_cellμ]; exact hdat.memL2.2.1
  have hmη : MemLp uη 2 (cellμ c) := by rw [← cellMeas_eq_cellμ]; exact hdat.memL2.2.2
  exact ⟨ae_cellMeas_of_ae_cellμ hm0.coeFn_toLp,
    ae_cellMeas_of_ae_cellμ hmq.coeFn_toLp,
    ae_cellMeas_of_ae_cellμ hmη.coeFn_toLp⟩

lemma H1Sol.isRealCylH1Datum {c : ℝ} (p : H1Sol c) :
    F8Ex.IsRealCylH1Datum c
      (val0CLM c p : Plane → F8Ex.RMerid)
      (dqCLM c p : Plane → F8Ex.RMerid)
      (detaCLM c p : Plane → F8Ex.RMerid) where
  weak_q := H1Sol.weak_q p
  weak_eta := H1Sol.weak_eta p
  solenoidal := (mem_divFree_iff_solenoidal (val0CLM c p)).1 (H1Sol.mem_divFree p)
  memL2 := by
    let g0 : Plane → F8Ex.RMerid := val0CLM c p
    let gq : Plane → F8Ex.RMerid := dqCLM c p
    let gη : Plane → F8Ex.RMerid := detaCLM c p
    have h0 : MemLp g0 2 (F8Ex.cellMeas c) := by
      have h : MemLp g0 2 (cellμ c) := Lp.memLp _
      rwa [cellMeas_eq_cellμ]
    have hq : MemLp gq 2 (F8Ex.cellMeas c) := by
      have h : MemLp gq 2 (cellμ c) := Lp.memLp _
      rwa [cellMeas_eq_cellμ]
    have hη : MemLp gη 2 (F8Ex.cellMeas c) := by
      have h : MemLp gη 2 (cellμ c) := Lp.memLp _
      rwa [cellMeas_eq_cellμ]
    exact ⟨h0, hq, hη⟩

/-! ## 2. Free evolution `freeH1CLM` and Duhamel smoothing family `duhH1CLM` -/

def freeH1Fun {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) : H1Sol c :=
  H1Sol.mkOfWeak
    (centeredHeatVecL2CLM hc θ (val0CLM c p))
    (centeredHeatVecL2CLM hc θ (dqCLM c p))
    (centeredHeatVecL2CLM hc θ (detaCLM c p))
    (by
      have hp0 : P0 c (val0CLM c p) = val0CLM c p :=
        UnforcedLeray.Cyl.P0_eq_self (H1Sol.mem_divFree p)
      have hc0 := centeredHeatVecL2CLM_P0_comm hc θ (val0CLM c p)
      rw [hp0] at hc0
      rw [hc0]
      exact UnforcedLeray.Cyl.P0_mem _)
    (hasWeakCellDerivR_centeredHeatVecL2CLM hc θ (H1Sol.weak_q p))
    (hasWeakCellDerivR_centeredHeatVecL2CLM hc θ (H1Sol.weak_eta p))

lemma norm_freeH1Fun_le {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    ‖freeH1Fun hc θ p‖ ≤ 1 * ‖p‖ := by
  rw [one_mul]
  change max ‖centeredHeatVecL2CLM hc θ (val0CLM c p)‖
    (max ‖centeredHeatVecL2CLM hc θ (dqCLM c p)‖
      ‖centeredHeatVecL2CLM hc θ (detaCLM c p)‖) ≤ ‖p‖
  have b0 : ‖centeredHeatVecL2CLM hc θ (val0CLM c p)‖ ≤ ‖p‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_centeredHeatVecL2CLM_le_one_all hc θ))).trans
      (norm_val0CLM_le p)
  have bq : ‖centeredHeatVecL2CLM hc θ (dqCLM c p)‖ ≤ ‖p‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_centeredHeatVecL2CLM_le_one_all hc θ))).trans
      (norm_dqCLM_le p)
  have bη : ‖centeredHeatVecL2CLM hc θ (detaCLM c p)‖ ≤ ‖p‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_centeredHeatVecL2CLM_le_one_all hc θ))).trans
      (norm_detaCLM_le p)
  exact max_le b0 (max_le bq bη)

def freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) : H1Sol c →L[ℝ] H1Sol c :=
  LinearMap.mkContinuous
    { toFun := freeH1Fun hc θ
      map_add' := fun p q => by
        apply Subtype.ext
        dsimp [freeH1Fun, H1Sol.mkOfWeak]
        simp only [map_add]
      map_smul' := fun r p => by
        apply Subtype.ext
        dsimp [freeH1Fun, H1Sol.mkOfWeak]
        simp only [map_smul] }
    1 (norm_freeH1Fun_le hc θ)

@[simp] lemma val0_freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    val0CLM c (freeH1CLM hc θ p) = centeredHeatVecL2CLM hc θ (val0CLM c p) := rfl
@[simp] lemma dq_freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    dqCLM c (freeH1CLM hc θ p) = centeredHeatVecL2CLM hc θ (dqCLM c p) := rfl
@[simp] lemma deta_freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    detaCLM c (freeH1CLM hc θ p) = centeredHeatVecL2CLM hc θ (detaCLM c p) := rfl

lemma freeH1CLM_of_nonpos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : θ ≤ 0) :
    freeH1CLM hc θ = ContinuousLinearMap.id ℝ (H1Sol c) := by
  apply ContinuousLinearMap.ext
  intro p
  apply H1Sol.ext_val0 hc
  change val0CLM c (freeH1CLM hc θ p) = val0CLM c p
  rw [val0_freeH1CLM, centeredHeatVecL2CLM_eq_id_of_nonpos hc hθ]
  rfl

lemma norm_freeH1CLM_le {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖freeH1CLM hc θ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma continuous_freeH1CLM_apply {c : ℝ} (hc : 0 < c) (p : H1Sol c) :
    Continuous (fun θ : ℝ => freeH1CLM hc θ p) := by
  rw [continuous_induced_rng]
  exact (continuous_centeredHeatVecL2CLM_apply hc (val0CLM c p)).prodMk
    ((continuous_centeredHeatVecL2CLM_apply hc (dqCLM c p)).prodMk
      (continuous_centeredHeatVecL2CLM_apply hc (detaCLM c p)))

def duhH1FunPos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) : H1Sol c :=
  let hw := hasWeakCellDerivR_P0 hc
    (hasWeakCellDerivR_DHeatCLM hc 0 hθ f) (hasWeakCellDerivR_DHeatCLM hc 1 hθ f)
  H1Sol.mkOfWeak
    (P0 c (centeredHeatVecL2CLM hc θ f))
    (P0 c (DHeatCLM hc 0 θ f))
    (P0 c (DHeatCLM hc 1 θ f))
    (UnforcedLeray.Cyl.P0_mem _) hw.1 hw.2

lemma norm_duhH1FunPos_le {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    ‖duhH1FunPos hc hθ f‖ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ := by
  change max ‖P0 c (centeredHeatVecL2CLM hc θ f)‖
    (max ‖P0 c (DHeatCLM hc 0 θ f)‖ ‖P0 c (DHeatCLM hc 1 θ f)‖) ≤ _
  have hP0 : ∀ z : L2v c, ‖P0 c z‖ ≤ ‖z‖ := fun z =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) UnforcedLeray.Cyl.norm_P0_le)
  have b0 : ‖P0 c (centeredHeatVecL2CLM hc θ f)‖ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ := by
    calc ‖P0 c (centeredHeatVecL2CLM hc θ f)‖
        ≤ ‖centeredHeatVecL2CLM hc θ f‖ := hP0 _
      _ ≤ 1 * ‖f‖ := (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_centeredHeatVecL2CLM_le_one_all hc θ) (norm_nonneg _))
      _ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have bj : ∀ j : Fin 2, ‖P0 c (DHeatCLM hc j θ f)‖ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ := by
    intro j
    calc ‖P0 c (DHeatCLM hc j θ f)‖
        ≤ ‖DHeatCLM hc j θ f‖ := hP0 _
      _ ≤ heatDivL2Coeff θ * ‖f‖ := (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_DHeatCLM_le hc j hθ) (norm_nonneg _))
      _ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  exact max_le b0 (max_le (bj 0) (bj 1))

def duhH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) : L2v c →L[ℝ] H1Sol c :=
  if hθ : 0 < θ then
    LinearMap.mkContinuous
      { toFun := duhH1FunPos hc hθ
        map_add' := fun f g => by
          apply Subtype.ext
          dsimp [duhH1FunPos, H1Sol.mkOfWeak]
          simp only [map_add]
        map_smul' := fun r f => by
          apply Subtype.ext
          dsimp [duhH1FunPos, H1Sol.mkOfWeak]
          simp only [map_smul] }
      (max 1 (heatDivL2Coeff θ))
      (norm_duhH1FunPos_le hc hθ)
  else 0

lemma val0_duhH1CLM_of_pos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    val0CLM c (duhH1CLM hc θ f) = P0 c (centeredHeatVecL2CLM hc θ f) := by
  simp [duhH1CLM, hθ, duhH1FunPos, H1Sol.mkOfWeak]

lemma dq_duhH1CLM_of_pos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    dqCLM c (duhH1CLM hc θ f) = P0 c (DHeatCLM hc 0 θ f) := by
  simp [duhH1CLM, hθ, duhH1FunPos, H1Sol.mkOfWeak]

lemma deta_duhH1CLM_of_pos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    detaCLM c (duhH1CLM hc θ f) = P0 c (DHeatCLM hc 1 θ f) := by
  simp [duhH1CLM, hθ, duhH1FunPos, H1Sol.mkOfWeak]

lemma norm_duhH1CLM_le {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) :
    ‖duhH1CLM hc θ‖ ≤ max 1 (heatDivL2Coeff θ) := by
  simp only [duhH1CLM, hθ, ↓reduceDIte]
  exact LinearMap.mkContinuous_norm_le _ (le_trans zero_le_one (le_max_left _ _)) _

lemma continuousOn_duhH1CLM_apply {c : ℝ} (hc : 0 < c) (f : L2v c) :
    ContinuousOn (fun θ : ℝ => duhH1CLM hc θ f) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  rw [continuous_induced_rng]
  have h0 : Continuous (fun θ : Ioi (0 : ℝ) => P0 c (centeredHeatVecL2CLM hc θ.1 f)) :=
    (P0 c).continuous.comp ((continuous_centeredHeatVecL2CLM_apply hc f).comp continuous_subtype_val)
  have hq : Continuous (fun θ : Ioi (0 : ℝ) => P0 c (DHeatCLM hc 0 θ.1 f)) :=
    (P0 c).continuous.comp (continuousOn_iff_continuous_domRestrict.1 (continuousOn_DHeatCLM_apply hc 0 f))
  have hη : Continuous (fun θ : Ioi (0 : ℝ) => P0 c (DHeatCLM hc 1 θ.1 f)) :=
    (P0 c).continuous.comp (continuousOn_iff_continuous_domRestrict.1 (continuousOn_DHeatCLM_apply hc 1 f))
  refine (h0.prodMk (hq.prodMk hη)).congr fun θ => ?_
  have hpos : 0 < θ.1 := θ.2
  simp [duhH1CLM, hpos, duhH1FunPos, H1Sol.mkOfWeak]

/-! ## 3. Bounded strongly continuous Oseen drift operator `bvCLM` -/

private lemma memLp_scalarMult_cellμ {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hb : ∀ y, |a y| ≤ M) (f : L2v c) :
    MemLp (fun y => a y • (f : Plane → Vec2) y) 2 (cellμ c) := by
  let g : Plane → F8Ex.RMerid := f
  have hg : MemLp g 2 (F8Ex.cellMeas c) := by
    have hg0 : MemLp g 2 (cellμ c) := Lp.memLp f
    rwa [cellMeas_eq_cellμ]
  have hm : MemLp (fun y => a y • g y) 2 (F8Ex.cellMeas c) := F8Ex.memLp_mulRealR ha hb hg
  change MemLp (fun y => a y • g y) 2 (cellμ c)
  rwa [← cellMeas_eq_cellμ]

private lemma norm_scalarMult_le {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) (f : L2v c) :
    ‖(memLp_scalarMult_cellμ ha hb f).toLp (fun y => a y • (f : Plane → Vec2) y)‖ ≤ M * ‖f‖ := by
  let hm := memLp_scalarMult_cellμ ha hb f
  let g : L2v c := hm.toLp (fun y => a y • (f : Plane → Vec2) y)
  have hinner_le : ⟪g, g⟫_ℝ ≤ M ^ 2 * ⟪f, f⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
    have hif := L2.integrable_inner (𝕜 := ℝ) f f
    have hig := L2.integrable_inner (𝕜 := ℝ) g g
    refine integral_mono_ae hig (hif.const_mul (M ^ 2)) ?_
    filter_upwards [hm.coeFn_toLp] with y hy
    change ⟪g y, g y⟫_ℝ ≤ M ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ
    rw [hy, real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
    have hsq : a y * a y ≤ M ^ 2 := by
      have h1 : |a y| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb y) 2
      simpa [sq_abs, sq] using h1
    exact mul_le_mul_of_nonneg_right hsq real_inner_self_nonneg
  rw [norm_eq_sqrt_real_inner g, norm_eq_sqrt_real_inner f]
  calc Real.sqrt ⟪g, g⟫_ℝ
      ≤ Real.sqrt (M ^ 2 * ⟪f, f⟫_ℝ) := Real.sqrt_le_sqrt hinner_le
    _ = M * Real.sqrt ⟪f, f⟫_ℝ := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

def scalarMultCLM {c : ℝ} (a : Plane → ℝ) (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) : L2v c →L[ℝ] L2v c :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        (memLp_scalarMult_cellμ ha hb f).toLp (fun y => a y • (f : Plane → Vec2) y)
      map_add' := fun f₁ f₂ => by
        apply Lp.ext
        let hm1 := memLp_scalarMult_cellμ ha hb f₁
        let hm2 := memLp_scalarMult_cellμ ha hb f₂
        let hm12 := memLp_scalarMult_cellμ ha hb (f₁ + f₂)
        filter_upwards [hm12.coeFn_toLp, Lp.coeFn_add (hm1.toLp _) (hm2.toLp _),
          hm1.coeFn_toLp, hm2.coeFn_toLp, Lp.coeFn_add f₁ f₂] with y h12 hadd h1 h2 hfadd
        rw [h12, hfadd, Pi.add_apply, smul_add, hadd, Pi.add_apply, h1, h2]
      map_smul' := fun r f => by
        apply Lp.ext
        let hm := memLp_scalarMult_cellμ ha hb f
        let hmr := memLp_scalarMult_cellμ ha hb (r • f)
        simp only [RingHom.id_apply]
        filter_upwards [hmr.coeFn_toLp, Lp.coeFn_smul r (hm.toLp _),
          hm.coeFn_toLp, Lp.coeFn_smul r f] with y hr1 hr2 h1 hf
        rw [hr1, hf, Pi.smul_apply, smul_comm, hr2, Pi.smul_apply, h1] }
    M (norm_scalarMult_le ha hM hb)

lemma coeFn_scalarMultCLM {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) (f : L2v c) :
    (scalarMultCLM a ha hM hb f : Plane → Vec2) =ᵐ[cellμ c] fun y => a y • (f : Plane → Vec2) y :=
  (memLp_scalarMult_cellμ ha hb f).coeFn_toLp

lemma norm_scalarMultCLM_le {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) :
    ‖scalarMultCLM (c := c) a ha hM hb‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

lemma continuous_scalarMultCLM_apply {c : ℝ} {a : ℝ → Plane → ℝ}
    (ha : Continuous (Function.uncurry a))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ r y, |a r y| ≤ M) (f : L2v c) :
    Continuous (fun r : ℝ =>
      scalarMultCLM (a r) (ha.comp (continuous_const.prodMk continuous_id)) hM (hb r) f) := by
  have ha_r : ∀ r : ℝ, Continuous (a r) :=
    fun r => ha.comp (continuous_const.prodMk continuous_id)
  rw [continuous_iff_continuousAt]
  intro r₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let F : ℝ → L2v c := fun r => scalarMultCLM (a r) (ha_r r) hM (hb r) f
  change Tendsto (fun r => ‖F r - F r₀‖) (𝓝 r₀) (𝓝 0)
  have hnorm_eq : ∀ r : ℝ, ‖F r - F r₀‖ =
      Real.sqrt (∫ y : Plane, (a r y - a r₀ y) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ
        ∂(cellμ c)) := by
    intro r
    rw [norm_eq_sqrt_real_inner (F r - F r₀)]
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have hr := coeFn_scalarMultCLM (ha_r r) hM (hb r) f
    have hr₀ := coeFn_scalarMultCLM (ha_r r₀) hM (hb r₀) f
    filter_upwards [Lp.coeFn_sub (F r) (F r₀), hr, hr₀] with y hsub h1 h2
    change ⟪((F r - F r₀ : L2v c) : Plane → Vec2) y, ((F r - F r₀ : L2v c) : Plane → Vec2) y⟫_ℝ = _
    rw [hsub, Pi.sub_apply, h1, h2, ← sub_smul, real_inner_smul_left, real_inner_smul_right,
      ← mul_assoc, sq]
  simp_rw [hnorm_eq]
  have hsqrt0 : Real.sqrt 0 = 0 := Real.sqrt_zero
  rw [← hsqrt0]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  have hint_dom : Integrable
      (fun y : Plane => (2 * M) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ) (cellμ c) :=
    (L2.integrable_inner (𝕜 := ℝ) f f).const_mul ((2 * M) ^ 2)
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := cellμ c)
    (F := fun r y => (a r y - a r₀ y) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ)
    (bound := fun y => (2 * M) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ)
    (f := fun _ => 0)
    (Eventually.of_forall fun r => by
      have hc1 : Continuous (fun y : Plane => (a r y - a r₀ y) ^ 2) :=
        ((ha_r r).sub (ha_r r₀)).pow 2
      exact hc1.aestronglyMeasurable.mul
        (L2.integrable_inner (𝕜 := ℝ) f f).aestronglyMeasurable)
    (Eventually.of_forall fun r => Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) real_inner_self_nonneg)]
      have hab : |a r y - a r₀ y| ≤ 2 * M := by
        calc |a r y - a r₀ y| ≤ |a r y| + |a r₀ y| := abs_sub _ _
          _ ≤ M + M := add_le_add (hb r y) (hb r₀ y)
          _ = 2 * M := by ring
      have hsq : (a r y - a r₀ y) ^ 2 ≤ (2 * M) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
      exact mul_le_mul_of_nonneg_right hsq real_inner_self_nonneg)
    hint_dom
    (Eventually.of_forall fun y => by
      have hcy : Continuous (fun r : ℝ => (a r y - a r₀ y) ^ 2 *
          ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ) :=
        (((ha.comp (continuous_id.prodMk continuous_const)).sub continuous_const).pow 2).mul
          continuous_const
      simpa using hcy.tendsto r₀)
  simpa using hlim

private def rank1VecCLM (j i : Fin 2) : Vec2 →L[ℝ] Vec2 :=
  (F8Ex.πR j).smulRight (EuclideanSpace.single i (1 : ℝ))

private lemma norm_rank1VecCLM_le (j i : Fin 2) : ‖rank1VecCLM j i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, rank1VecCLM, ContinuousLinearMap.smulRight_apply, norm_smul, Real.norm_eq_abs]
  have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : Vec2)‖ = 1 := by
    fin_cases i <;> simp
  rw [h1, mul_one]
  exact PiLp.norm_apply_le v j

private def clamp02 (r : ℝ) : ℝ := (Set.projIcc (0 : ℝ) 2 (by norm_num) r : ℝ)

private lemma clamp02_mem (r : ℝ) : clamp02 r ∈ Icc (0 : ℝ) 2 :=
  (Set.projIcc (0 : ℝ) 2 (by norm_num) r).2

private lemma clamp02_of_mem {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 2) : clamp02 r = r := by
  simp [clamp02, Set.projIcc_of_mem _ hr]

private lemma continuous_clamp02 : Continuous clamp02 :=
  continuous_subtype_val.comp continuous_projIcc

private lemma fderiv_drift_eq_fderivWithin {c : ℝ} {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2)
    (j i : Fin 2) (y : Plane) :
    fderiv ℝ (fun z => V s z i) y (B0579.dir j) =
      F8Ex.πR i (fderivWithin ℝ (fun x : Coord => V x.1 x.2)
        (Icc (0 : ℝ) 2 ×ˢ univ) (s, y) ((0 : ℝ), B0579.dir j)) := by
  let S : Set Coord := Icc (0 : ℝ) 2 ×ˢ univ
  have hU : UniqueDiffOn ℝ S :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 2)) uniqueDiffOn_univ
  have hxS : (s, y) ∈ S := ⟨hs, mem_univ y⟩
  have hdV : DifferentiableWithinAt ℝ (fun x : Coord => V x.1 x.2) S (s, y) :=
    (hV.smooth.contDiffWithinAt hxS).differentiableWithinAt (by simp)
  let ι : Plane → Coord := fun z => (s, z)
  have hι : HasFDerivWithinAt ι
      ((0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Plane)) univ y :=
    hasFDerivWithinAt_univ.2 ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))
  have hmaps : MapsTo ι univ S := fun z _ => ⟨hs, mem_univ z⟩
  have hcomp : HasFDerivAt (V s)
      ((fderivWithin ℝ (fun x : Coord => V x.1 x.2) S (s, y)).comp
        ((0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Plane))) y :=
    hasFDerivWithinAt_univ.1 (hdV.hasFDerivWithinAt.comp y hι hmaps)
  have hcomp_i : HasFDerivAt (fun z => V s z i)
      ((F8Ex.πR i).comp ((fderivWithin ℝ (fun x : Coord => V x.1 x.2) S (s, y)).comp
        ((0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Plane)))) y :=
    (F8Ex.πR i).hasFDerivAt.comp y hcomp
  rw [hcomp_i.fderiv]
  rfl

private lemma drift_clamped_coeffs {c : ℝ} {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ j : Fin 2, Continuous (Function.uncurry fun r (y : Plane) => V (clamp02 r) y j)) ∧
      (∀ j i : Fin 2, Continuous (Function.uncurry fun r (y : Plane) =>
        fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j))) ∧
      (∀ r : ℝ, ∀ j : Fin 2, ∀ y : Plane, |V (clamp02 r) y j| ≤ M) ∧
      (∀ r : ℝ, ∀ j i : Fin 2, ∀ y : Plane,
        |fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j)| ≤ M) := by
  obtain ⟨M0, hM0_nn, hM0⟩ := hV.deriv_bound 0
  obtain ⟨M1, _, hM1⟩ := hV.deriv_bound 1
  let M := max M0 M1
  have hM_nn : 0 ≤ M := le_trans hM0_nn (le_max_left M0 M1)
  let S : Set Coord := Icc (0 : ℝ) 2 ×ˢ univ
  have hU : UniqueDiffOn ℝ S :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 2)) uniqueDiffOn_univ
  have hc_cl : Continuous (fun p : ℝ × Plane => ((clamp02 p.1, p.2) : Coord)) :=
    (continuous_clamp02.comp continuous_fst).prodMk continuous_snd
  have hm_cl : ∀ p : ℝ × Plane, ((clamp02 p.1, p.2) : Coord) ∈ S :=
    fun p => ⟨clamp02_mem p.1, mem_univ p.2⟩
  have hcont_V : ∀ j : Fin 2, Continuous (fun p : ℝ × Plane => V (clamp02 p.1) p.2 j) := by
    intro j
    exact (F8Ex.πR j).continuous.comp (hV.smooth.continuousOn.comp_continuous hc_cl hm_cl)
  have hcont_dV : ∀ j i : Fin 2, Continuous (fun p : ℝ × Plane =>
      fderiv ℝ (fun z => V (clamp02 p.1) z i) p.2 (B0579.dir j)) := by
    intro j i
    have hfd_on := hV.smooth.continuousOn_fderivWithin_apply hU (by simp)
    have hc_arg : Continuous (fun p : ℝ × Plane =>
        (((clamp02 p.1, p.2) : Coord), ((0 : ℝ), B0579.dir j))) :=
      hc_cl.prodMk continuous_const
    have hm_arg : ∀ p : ℝ × Plane,
        (((clamp02 p.1, p.2) : Coord), ((0 : ℝ), B0579.dir j)) ∈ S ×ˢ (univ : Set Coord) :=
      fun p => ⟨hm_cl p, mem_univ _⟩
    have hc1 := (F8Ex.πR i).continuous.comp (hfd_on.comp_continuous hc_arg hm_arg)
    refine hc1.congr fun p => ?_
    exact (fderiv_drift_eq_fderivWithin hV (clamp02_mem p.1) j i p.2).symm
  refine ⟨M, hM_nn, hcont_V, hcont_dV, ?_, ?_⟩
  · intro r j y
    calc |V (clamp02 r) y j| = ‖V (clamp02 r) y j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖V (clamp02 r) y‖ := PiLp.norm_apply_le _ j
      _ = ‖iteratedFDeriv ℝ 0 (V (clamp02 r)) y‖ := (norm_iteratedFDeriv_zero).symm
      _ ≤ M0 := hM0 (clamp02 r) (clamp02_mem r) y
      _ ≤ M := le_max_left M0 M1
  · intro r j i y
    have hVs : ContDiff ℝ ∞ (V (clamp02 r)) := by
      have hc := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (s := univ) (fun z _ => ⟨clamp02_mem r, mem_univ z⟩)
      exact contDiffOn_univ.1 hc
    have hproj : fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j) =
        fderiv ℝ (V (clamp02 r)) y (B0579.dir j) i := by
      have hc := ((F8Ex.πR i).hasFDerivAt.comp y
        (hVs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change fderiv ℝ ((F8Ex.πR i) ∘ (V (clamp02 r))) y (B0579.dir j) =
        F8Ex.πR i (fderiv ℝ (V (clamp02 r)) y (B0579.dir j))
      rw [hc, ContinuousLinearMap.comp_apply]
    have hdir_norm : ‖B0579.dir j‖ = 1 := by fin_cases j <;> simp [B0579.dir]
    rw [hproj]
    calc |fderiv ℝ (V (clamp02 r)) y (B0579.dir j) i|
        = ‖fderiv ℝ (V (clamp02 r)) y (B0579.dir j) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (V (clamp02 r)) y (B0579.dir j)‖ := PiLp.norm_apply_le _ i
      _ = ‖iteratedFDeriv ℝ 1 (V (clamp02 r)) y ![B0579.dir j]‖ := by
          rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
      _ ≤ ‖iteratedFDeriv ℝ 1 (V (clamp02 r)) y‖ *
            ∏ l : Fin 1, ‖(![B0579.dir j] : Fin 1 → Plane) l‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (V (clamp02 r)) y‖ := by simp [hdir_norm]
      _ ≤ M1 := hM1 (clamp02 r) (clamp02_mem r) y
      _ ≤ M := le_max_right M0 M1

def driftBound {c : ℝ} {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) : ℝ :=
  (drift_clamped_coeffs hV).choose

lemma driftBound_nonneg {c : ℝ} {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) :
    0 ≤ driftBound hV :=
  (drift_clamped_coeffs hV).choose_spec.1

def bvCLM {c : ℝ} (_hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (r : ℝ) : H1Sol c →L[ℝ] L2v c :=
  let hspec := (drift_clamped_coeffs hV).choose_spec
  let hM := hspec.1
  let hcV := hspec.2.1
  let hcdV := hspec.2.2.1
  let hbV := hspec.2.2.2.1
  let hbdV := hspec.2.2.2.2
  let tq := (scalarMultCLM (fun y => V (clamp02 r) y 0)
    ((hcV 0).comp (continuous_const.prodMk continuous_id)) hM (hbV r 0)).comp (dqCLM c)
  let tη := (scalarMultCLM (fun y => V (clamp02 r) y 1)
    ((hcV 1).comp (continuous_const.prodMk continuous_id)) hM (hbV r 1)).comp (detaCLM c)
  let ts (j i : Fin 2) := (scalarMultCLM
    (fun y => fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j))
    ((hcdV j i).comp (continuous_const.prodMk continuous_id)) hM (hbdV r j i)).comp
    (((rank1VecCLM j i).compLpL 2 (cellμ c)).comp (val0CLM c))
  ((tq + tη) + (ts 0 0 + ts 0 1)) + (ts 1 0 + ts 1 1)

lemma norm_bvCLM_le {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (r : ℝ) :
    ‖bvCLM hc hV r‖ ≤ 6 * driftBound hV := by
  let M := driftBound hV
  have hM : 0 ≤ M := driftBound_nonneg hV
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  let hspec := (drift_clamped_coeffs hV).choose_spec
  have hcV_r : ∀ j : Fin 2, Continuous (fun y : Plane => V (clamp02 r) y j) :=
    fun j => (hspec.2.1 j).comp (continuous_const.prodMk continuous_id)
  have hcdV_r : ∀ j i : Fin 2,
      Continuous (fun y : Plane => fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j)) :=
    fun j i => (hspec.2.2.1 j i).comp (continuous_const.prodMk continuous_id)
  have b_sc : ∀ {a : Plane → ℝ} (ha : Continuous a) (hb : ∀ y, |a y| ≤ M) (z : L2v c),
      ‖z‖ ≤ ‖p‖ → ‖scalarMultCLM a ha hM hb z‖ ≤ M * ‖p‖ := by
    intro a ha hb z hz
    exact ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_scalarMultCLM_le ha hM hb) (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hz hM)
  have b_rk : ∀ j i : Fin 2,
      ‖((rank1VecCLM j i).compLpL 2 (cellμ c)) (val0CLM c p)‖ ≤ ‖p‖ := by
    intro j i
    calc ‖((rank1VecCLM j i).compLpL 2 (cellμ c)) (val0CLM c p)‖
        ≤ ‖(rank1VecCLM j i).compLpL 2 (cellμ c)‖ * ‖val0CLM c p‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖val0CLM c p‖ :=
          mul_le_mul_of_nonneg_right
            ((ContinuousLinearMap.norm_compLpL_le (rank1VecCLM j i)).trans (norm_rank1VecCLM_le j i))
            (norm_nonneg _)
      _ = ‖val0CLM c p‖ := one_mul _
      _ ≤ ‖p‖ := norm_val0CLM_le p
  let tq := scalarMultCLM (fun y => V (clamp02 r) y 0) (hcV_r 0) hM (hspec.2.2.2.1 r 0) (dqCLM c p)
  let tη := scalarMultCLM (fun y => V (clamp02 r) y 1) (hcV_r 1) hM (hspec.2.2.2.1 r 1) (detaCLM c p)
  let ts (j i : Fin 2) := scalarMultCLM
    (fun y => fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j))
    (hcdV_r j i) hM (hspec.2.2.2.2 r j i)
    (((rank1VecCLM j i).compLpL 2 (cellμ c)) (val0CLM c p))
  have h_eq : bvCLM hc hV r p = ((tq + tη) + (ts 0 0 + ts 0 1)) + (ts 1 0 + ts 1 1) := rfl
  rw [h_eq]
  have b1 : ‖tq‖ ≤ M * ‖p‖ := b_sc (hcV_r 0) (hspec.2.2.2.1 r 0) (dqCLM c p) (norm_dqCLM_le p)
  have b2 : ‖tη‖ ≤ M * ‖p‖ := b_sc (hcV_r 1) (hspec.2.2.2.1 r 1) (detaCLM c p) (norm_detaCLM_le p)
  have b3 : ‖ts 0 0‖ ≤ M * ‖p‖ := b_sc (hcdV_r 0 0) (hspec.2.2.2.2 r 0 0) _ (b_rk 0 0)
  have b4 : ‖ts 0 1‖ ≤ M * ‖p‖ := b_sc (hcdV_r 0 1) (hspec.2.2.2.2 r 0 1) _ (b_rk 0 1)
  have b5 : ‖ts 1 0‖ ≤ M * ‖p‖ := b_sc (hcdV_r 1 0) (hspec.2.2.2.2 r 1 0) _ (b_rk 1 0)
  have b6 : ‖ts 1 1‖ ≤ M * ‖p‖ := b_sc (hcdV_r 1 1) (hspec.2.2.2.2 r 1 1) _ (b_rk 1 1)
  calc
    ‖((tq + tη) + (ts 0 0 + ts 0 1)) + (ts 1 0 + ts 1 1)‖
        ≤ ‖(tq + tη) + (ts 0 0 + ts 0 1)‖ + ‖ts 1 0 + ts 1 1‖ := norm_add_le _ _
    _ ≤ (‖tq + tη‖ + ‖ts 0 0 + ts 0 1‖) + (‖ts 1 0‖ + ‖ts 1 1‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ ((‖tq‖ + ‖tη‖) + (‖ts 0 0‖ + ‖ts 0 1‖)) + (‖ts 1 0‖ + ‖ts 1 1‖) :=
          add_le_add (add_le_add (norm_add_le _ _) (norm_add_le _ _)) le_rfl
    _ ≤ ((M * ‖p‖ + M * ‖p‖) + (M * ‖p‖ + M * ‖p‖)) + (M * ‖p‖ + M * ‖p‖) :=
          add_le_add (add_le_add (add_le_add b1 b2) (add_le_add b3 b4)) (add_le_add b5 b6)
    _ = 6 * M * ‖p‖ := by ring

lemma continuous_bvCLM_apply {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (p : H1Sol c) :
    Continuous (fun r : ℝ => bvCLM hc hV r p) := by
  let hspec := (drift_clamped_coeffs hV).choose_spec
  have c1 := continuous_scalarMultCLM_apply (hspec.2.1 0) hspec.1 (fun r => hspec.2.2.2.1 r 0)
    (dqCLM c p)
  have c2 := continuous_scalarMultCLM_apply (hspec.2.1 1) hspec.1 (fun r => hspec.2.2.2.1 r 1)
    (detaCLM c p)
  have c3 := continuous_scalarMultCLM_apply (hspec.2.2.1 0 0) hspec.1
    (fun r => hspec.2.2.2.2 r 0 0) (((rank1VecCLM 0 0).compLpL 2 (cellμ c)) (val0CLM c p))
  have c4 := continuous_scalarMultCLM_apply (hspec.2.2.1 0 1) hspec.1
    (fun r => hspec.2.2.2.2 r 0 1) (((rank1VecCLM 0 1).compLpL 2 (cellμ c)) (val0CLM c p))
  have c5 := continuous_scalarMultCLM_apply (hspec.2.2.1 1 0) hspec.1
    (fun r => hspec.2.2.2.2 r 1 0) (((rank1VecCLM 1 0).compLpL 2 (cellμ c)) (val0CLM c p))
  have c6 := continuous_scalarMultCLM_apply (hspec.2.2.1 1 1) hspec.1
    (fun r => hspec.2.2.2.2 r 1 1) (((rank1VecCLM 1 1).compLpL 2 (cellμ c)) (val0CLM c p))
  exact (((c1.add c2).add (c3.add c4)).add (c5.add c6)).congr (fun _ => rfl)

lemma bvCLM_ae_realBvSlice {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 2) (p : H1Sol c) :
    (bvCLM hc hV r p : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c]
      F8Ex.realBvSlice (V r) (val0CLM c p : Plane → F8Ex.RMerid)
        (dqCLM c p : Plane → F8Ex.RMerid) (detaCLM c p : Plane → F8Ex.RMerid) := by
  apply ae_cellMeas_of_ae_cellμ
  let hspec := (drift_clamped_coeffs hV).choose_spec
  have hcV_r : ∀ j : Fin 2, Continuous (fun y : Plane => V (clamp02 r) y j) :=
    fun j => (hspec.2.1 j).comp (continuous_const.prodMk continuous_id)
  have hcdV_r : ∀ j i : Fin 2,
      Continuous (fun y : Plane => fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j)) :=
    fun j i => (hspec.2.2.1 j i).comp (continuous_const.prodMk continuous_id)
  let rk (j i : Fin 2) : L2v c := ((rank1VecCLM j i).compLpL 2 (cellμ c)) (val0CLM c p)
  let tq := scalarMultCLM (fun y => V (clamp02 r) y 0)
    (hcV_r 0) hspec.1 (hspec.2.2.2.1 r 0) (dqCLM c p)
  let tη := scalarMultCLM (fun y => V (clamp02 r) y 1)
    (hcV_r 1) hspec.1 (hspec.2.2.2.1 r 1) (detaCLM c p)
  let ts (j i : Fin 2) := scalarMultCLM
    (fun y => fderiv ℝ (fun z => V (clamp02 r) z i) y (B0579.dir j))
    (hcdV_r j i) hspec.1 (hspec.2.2.2.2 r j i) (rk j i)
  have h_eq : bvCLM hc hV r p = ((tq + tη) + (ts 0 0 + ts 0 1)) + (ts 1 0 + ts 1 1) := rfl
  rw [h_eq]
  have aq := coeFn_scalarMultCLM (hcV_r 0) hspec.1 (hspec.2.2.2.1 r 0) (dqCLM c p)
  have aη := coeFn_scalarMultCLM (hcV_r 1) hspec.1 (hspec.2.2.2.1 r 1) (detaCLM c p)
  have as00 := coeFn_scalarMultCLM (hcdV_r 0 0) hspec.1 (hspec.2.2.2.2 r 0 0) (rk 0 0)
  have as01 := coeFn_scalarMultCLM (hcdV_r 0 1) hspec.1 (hspec.2.2.2.2 r 0 1) (rk 0 1)
  have as10 := coeFn_scalarMultCLM (hcdV_r 1 0) hspec.1 (hspec.2.2.2.2 r 1 0) (rk 1 0)
  have as11 := coeFn_scalarMultCLM (hcdV_r 1 1) hspec.1 (hspec.2.2.2.2 r 1 1) (rk 1 1)
  have rk00 := ContinuousLinearMap.coeFn_compLpL (rank1VecCLM 0 0) (val0CLM c p)
  have rk01 := ContinuousLinearMap.coeFn_compLpL (rank1VecCLM 0 1) (val0CLM c p)
  have rk10 := ContinuousLinearMap.coeFn_compLpL (rank1VecCLM 1 0) (val0CLM c p)
  have rk11 := ContinuousLinearMap.coeFn_compLpL (rank1VecCLM 1 1) (val0CLM c p)
  filter_upwards [Lp.coeFn_add ((tq + tη) + (ts 0 0 + ts 0 1)) (ts 1 0 + ts 1 1),
    Lp.coeFn_add (tq + tη) (ts 0 0 + ts 0 1),
    Lp.coeFn_add tq tη, Lp.coeFn_add (ts 0 0) (ts 0 1), Lp.coeFn_add (ts 1 0) (ts 1 1),
    aq, aη, as00, as01, as10, as11, rk00, rk01, rk10, rk11]
    with y hA hB hC hD hE hq hη hs00 hs01 hs10 hs11 hr00 hr01 hr10 hr11
  rw [hA, Pi.add_apply, hB, Pi.add_apply, hC, Pi.add_apply, hD, Pi.add_apply, hE, Pi.add_apply,
    hq, hη, hs00, hs01, hs10, hs11]
  dsimp only [rk]
  rw [hr00, hr01, hr10, hr11, clamp02_of_mem hr]
  ext k
  have hd0 : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := rfl
  have hd1 : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := rfl
  fin_cases k <;>
    simp [F8Ex.realBvSlice, rank1VecCLM, F8Ex.πR, hd0, hd1] <;> ring

/-! ## 4. Rescaled `[0, 1]` Volterra data and `[0, 2]` evolution `E_oseen` -/

def oseenVolterraData {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) : VolterraData ℝ (H1Sol c) (L2v c) where
  S₀ τ := freeH1CLM hc (2 * ν * τ)
  S τ := (-2 : ℝ) • duhH1CLM hc (2 * ν * τ)
  B σ := bvCLM hc hV (2 * σ)
  M₀ := 1
  C₀ := 2 * max 1 ((2 / Real.sqrt Real.pi) * (2 * ν) ^ (-(1 / 2 : ℝ)))
  β := 6 * driftBound hV
  norm_S₀_le τ _ _ := norm_freeH1CLM_le hc (2 * ν * τ)
  norm_S_le τ hτ hτ1 := by
    have hpos : 0 < 2 * ν * τ := by positivity
    have h1rpow : 1 ≤ τ ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
    have hcoeff : heatDivL2Coeff (2 * ν * τ) =
        ((2 / Real.sqrt Real.pi) * (2 * ν) ^ (-(1 / 2 : ℝ))) * τ ^ (-(1 / 2 : ℝ)) := by
      rw [heatDivL2Coeff_eq_singular (by positivity : 0 < 2 * ν) hτ]
      ring
    have hmax : max 1 (heatDivL2Coeff (2 * ν * τ)) ≤
        max 1 ((2 / Real.sqrt Real.pi) * (2 * ν) ^ (-(1 / 2 : ℝ))) * τ ^ (-(1 / 2 : ℝ)) := by
      refine max_le ?_ ?_
      · calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ max 1 ((2 / Real.sqrt Real.pi) * (2 * ν) ^ (-(1 / 2 : ℝ))) * τ ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul (le_max_left _ _) h1rpow zero_le_one (le_trans zero_le_one (le_max_left _ _))
      · rw [hcoeff]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hτ.le _)
    rw [norm_smul, Real.norm_eq_abs, show |(-2 : ℝ)| = 2 by norm_num]
    calc (2 : ℝ) * ‖duhH1CLM hc (2 * ν * τ)‖
        ≤ 2 * (max 1 ((2 / Real.sqrt Real.pi) * (2 * ν) ^ (-(1 / 2 : ℝ))) * τ ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left ((norm_duhH1CLM_le hc hpos).trans hmax) zero_le_two
      _ = 2 * max 1 ((2 / Real.sqrt Real.pi) * (2 * ν) ^ (-(1 / 2 : ℝ))) * τ ^ (-(1 / 2 : ℝ)) := by
          ring
  norm_B_le σ := norm_bvCLM_le hc hV (2 * σ)
  continuousOn_S₀ p :=
    ((continuous_freeH1CLM_apply hc p).comp (continuous_const.mul continuous_id)).continuousOn
  continuousOn_S f := by
    have hm : ContinuousOn (fun τ : ℝ => 2 * ν * τ) (Ioc 0 1) :=
      continuousOn_const.mul continuousOn_id
    have hmaps : MapsTo (fun τ : ℝ => 2 * ν * τ) (Ioc 0 1) (Ioi 0) :=
      fun τ hτ => mul_pos (by positivity) hτ.1
    exact ((continuousOn_duhH1CLM_apply hc f).comp hm hmaps).const_smul (-2 : ℝ)
  continuous_B p :=
    (continuous_bvCLM_apply hc hV p).comp (continuous_const.mul continuous_id)

lemma oseenCompatible {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) :
    (oseenVolterraData hc hν hV).Compatible where
  S₀_comp_S₀ a b ha hb _ := by
    apply ContinuousLinearMap.ext
    intro p
    apply H1Sol.ext_val0 hc
    change val0CLM c (freeH1CLM hc (2 * ν * a) (freeH1CLM hc (2 * ν * b) p)) =
      val0CLM c (freeH1CLM hc (2 * ν * (a + b)) p)
    rw [val0_freeH1CLM, val0_freeH1CLM, val0_freeH1CLM]
    have hc1 := congrArg (fun L : L2v c →L[ℝ] L2v c => L (val0CLM c p))
      (centeredHeatVecL2CLM_comp_of_nonneg hc
        (by positivity : 0 ≤ 2 * ν * a) (by positivity : 0 ≤ 2 * ν * b))
    simpa [mul_add] using hc1
  S₀_comp_S a b ha hb _ := by
    apply ContinuousLinearMap.ext
    intro f
    apply H1Sol.ext_val0 hc
    change val0CLM c (freeH1CLM hc (2 * ν * a) ((-2 : ℝ) • duhH1CLM hc (2 * ν * b) f)) =
      val0CLM c ((-2 : ℝ) • duhH1CLM hc (2 * ν * (a + b)) f)
    have hb_pos : 0 < 2 * ν * b := by positivity
    have hab_pos : 0 < 2 * ν * (a + b) := by positivity
    simp only [map_smul, val0_freeH1CLM, val0_duhH1CLM_of_pos hc hb_pos,
      val0_duhH1CLM_of_pos hc hab_pos, centeredHeatVecL2CLM_P0_comm hc]
    congr 2
    have hc1 := congrArg (fun L : L2v c →L[ℝ] L2v c => L f)
      (centeredHeatVecL2CLM_comp_of_nonneg hc
        (by positivity : 0 ≤ 2 * ν * a) (by positivity : 0 ≤ 2 * ν * b))
    simpa [mul_add] using hc1

def E_oseen {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (t a : ℝ) : H1Sol c →L[ℝ] H1Sol c :=
  (oseenVolterraData hc hν hV).stripEvolution (t / 2) (a / 2)

lemma E_oseen_self {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (a : ℝ) :
    E_oseen hc hν hV a a = ContinuousLinearMap.id ℝ (H1Sol c) := by
  unfold E_oseen
  rw [(oseenVolterraData hc hν hV).stripEvolution_self (a / 2)]
  dsimp [oseenVolterraData]
  rw [mul_zero, freeH1CLM_of_nonpos hc le_rfl]

lemma continuousOn_E_oseen {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 2) (x : H1Sol c) :
    ContinuousOn (fun t => E_oseen hc hν hV t a x) (Icc a 2) := by
  refine ((oseenVolterraData hc hν hV).continuousOn_stripEvolution (a / 2) x).comp
    (continuousOn_id.div_const 2) ?_
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2, ha.1]⟩

lemma E_oseen_comp {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {a r t : ℝ}
    (ha : 0 ≤ a) (har : a ≤ r) (hrt : r ≤ t) (ht : t ≤ 2) :
    (E_oseen hc hν hV t r).comp (E_oseen hc hν hV r a) = E_oseen hc hν hV t a :=
  VolterraData.stripEvolution_comp (oseenCompatible hc hν hV)
    (by linarith) (by linarith) (by linarith)

private lemma stripEvolution_div_two {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : VolterraData ℝ E F) {a t : ℝ} (hat : a ≤ t) (ht : t ≤ a + 2) (x : E) :
    IntervalIntegrable
      (fun r => (-2⁻¹ : ℝ) • D.S (t / 2 - r / 2) (D.B (r / 2) (D.stripEvolution (r / 2) (a / 2) x)))
      volume a t ∧
    D.stripEvolution (t / 2) (a / 2) x = D.S₀ (t / 2 - a / 2) x -
      ∫ r in a..t, (-2⁻¹ : ℝ) •
        D.S (t / 2 - r / 2) (D.B (r / 2) (D.stripEvolution (r / 2) (a / 2) x)) := by
  let g : ℝ → E := fun σ => D.S (t / 2 - σ) (D.B σ (D.stripEvolution σ (a / 2) x))
  have hτ : t / 2 ∈ Icc (a / 2) (a / 2 + 1) := ⟨by linarith, by linarith⟩
  have hcs : ContinuousOn (fun σ => D.stripEvolution σ (a / 2) x) (Icc (a / 2) (t / 2)) :=
    (D.continuousOn_stripEvolution (a / 2) x).mono (Icc_subset_Icc_right hτ.2)
  have hint_σ : IntervalIntegrable g volume (a / 2) (t / 2) :=
    D.intervalIntegrable_integrand hτ.1 hτ.2 hcs
  have hint_mul : IntervalIntegrable (fun r => g (2⁻¹ * r)) volume a t := by
    have h1 := hint_σ.comp_mul_left (c := (2⁻¹ : ℝ)) enorm_ne_top enorm_ne_top
    have ha' : (a / 2) / (2⁻¹ : ℝ) = a := by ring
    have ht' : (t / 2) / (2⁻¹ : ℝ) = t := by ring
    rwa [ha', ht'] at h1
  have hdiv_eq : (fun r : ℝ => (-2⁻¹ : ℝ) • g (r / 2)) = fun r => (-2⁻¹ : ℝ) • g (2⁻¹ * r) := by
    funext r; congr 2; ring
  have hint_r : IntervalIntegrable (fun r => (-2⁻¹ : ℝ) • g (r / 2)) volume a t := by
    rw [hdiv_eq]
    exact hint_mul.smul (-2⁻¹ : ℝ)
  refine ⟨hint_r, ?_⟩
  have heq := D.stripEvolution_eq hτ x
  have hchg := intervalIntegral.integral_comp_div g (a := a) (b := t) (c := (2 : ℝ)) (by norm_num)
  have hc2 : (-2⁻¹ : ℝ) * (2 : ℝ) = -1 := by norm_num
  have hduhamel : (∫ r in a..t, (-2⁻¹ : ℝ) • g (r / 2)) = -(∫ σ in (a / 2)..(t / 2), g σ) := by
    rw [intervalIntegral.integral_smul, hchg, smul_smul, hc2, neg_one_smul]
  rw [heq, hduhamel, sub_neg_eq_add]

lemma E_oseen_mild {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ 2) (x : H1Sol c) :
    IntervalIntegrable
      (fun r => duhH1CLM hc (ν * (t - r)) (bvCLM hc hV r (E_oseen hc hν hV r a x)))
      volume a t ∧
    E_oseen hc hν hV t a x = freeH1CLM hc (ν * (t - a)) x -
      ∫ r in a..t, duhH1CLM hc (ν * (t - r)) (bvCLM hc hV r (E_oseen hc hν hV r a x)) := by
  obtain ⟨hint, heq⟩ :=
    stripEvolution_div_two (oseenVolterraData hc hν hV) hat (by linarith [ha, ht]) x
  have hc1 : (-2⁻¹ : ℝ) * (-2 : ℝ) = 1 := by norm_num
  have hS : ∀ r : ℝ,
      (-2⁻¹ : ℝ) • (oseenVolterraData hc hν hV).S (t / 2 - r / 2)
        ((oseenVolterraData hc hν hV).B (r / 2) (E_oseen hc hν hV r a x)) =
      duhH1CLM hc (ν * (t - r)) (bvCLM hc hV r (E_oseen hc hν hV r a x)) := by
    intro r
    change (-2⁻¹ : ℝ) • (((-2 : ℝ) • duhH1CLM hc (2 * ν * (t / 2 - r / 2)))
      (bvCLM hc hV (2 * (r / 2)) (E_oseen hc hν hV r a x))) = _
    have h1 : 2 * ν * (t / 2 - r / 2) = ν * (t - r) := by ring
    have h2 : 2 * (r / 2) = r := by ring
    rw [h1, h2, smul_apply, smul_smul, hc1, one_smul]
  have hS0 : (oseenVolterraData hc hν hV).S₀ (t / 2 - a / 2) x = freeH1CLM hc (ν * (t - a)) x := by
    change freeH1CLM hc (2 * ν * (t / 2 - a / 2)) x = _
    congr 2; ring
  have hfun : (fun r => (-2⁻¹ : ℝ) • (oseenVolterraData hc hν hV).S (t / 2 - r / 2)
      ((oseenVolterraData hc hν hV).B (r / 2)
        ((oseenVolterraData hc hν hV).stripEvolution (r / 2) (a / 2) x))) =
      fun r => duhH1CLM hc (ν * (t - r)) (bvCLM hc hV r (E_oseen hc hν hV r a x)) :=
    funext hS
  have heq' : E_oseen hc hν hV t a x = (oseenVolterraData hc hν hV).S₀ (t / 2 - a / 2) x -
      ∫ r in a..t, (-2⁻¹ : ℝ) • (oseenVolterraData hc hν hV).S (t / 2 - r / 2)
        ((oseenVolterraData hc hν hV).B (r / 2)
          ((oseenVolterraData hc hν hV).stripEvolution (r / 2) (a / 2) x)) := heq
  rw [hfun] at hint heq'
  rw [hS0] at heq'
  exact ⟨hint, heq'⟩

/-! ## 5. Weak Oseen identity for `E_oseen t 0 u₀` via heat FTC + Fubini -/

private lemma fubini_triangle_rpow_half {t C_ker : ℝ} (_ht_pos : 0 < t)
    {K : ℝ → ℝ → ℝ}
    (hK_contOn : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < t})
    (hC_ker_nn : 0 ≤ C_ker)
    (hK_bdd : ∀ r s : ℝ, 0 < r → r < s → s < t → |K r s| ≤ C_ker * (s - r) ^ (-(1 / 2 : ℝ))) :
    Integrable (fun s => ∫ r in (0 : ℝ)..s, K r s) (volume.restrict (Ioo 0 t)) ∧
      (∫ r in Ioo 0 t, ∫ s in r..t, K r s) = ∫ s in Ioo 0 t, ∫ r in (0 : ℝ)..s, K r s := by
  let T_open : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < t}
  have hT_open : IsOpen T_open :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  let G : ℝ × ℝ → ℝ := T_open.indicator (fun p => K p.1 p.2)
  let μI : Measure ℝ := volume.restrict (Ioo 0 t)
  have hG_meas' : AEStronglyMeasurable G (volume.prod volume) := by
    rw [aestronglyMeasurable_indicator_iff hT_open.measurableSet, ← Measure.volume_eq_prod]
    exact hK_contOn.aestronglyMeasurable hT_open.measurableSet
  have hG_meas_I : AEStronglyMeasurable G (μI.prod μI) := by
    rw [Measure.prod_restrict]
    exact hG_meas'.restrict
  have hG_bound : ∀ p : ℝ × ℝ, ‖G p‖ ≤
      T_open.indicator (fun p => C_ker * (p.2 - p.1) ^ (-(1 / 2 : ℝ))) p := by
    intro p
    by_cases hp : p ∈ T_open
    · dsimp only [G]
      rw [indicator_of_mem hp, indicator_of_mem hp, Real.norm_eq_abs]
      exact hK_bdd p.1 p.2 hp.1 hp.2.1 hp.2.2
    · simp only [G, indicator_of_notMem hp, norm_zero, le_rfl]
  have hG_int : Integrable G (μI.prod μI) := by
    rw [MeasureTheory.integrable_prod_iff hG_meas_I]
    have hslice_int : ∀ r ∈ Ioo (0 : ℝ) t, Integrable (fun s => G (r, s)) μI ∧
        ∫ s, ‖G (r, s)‖ ∂μI ≤ C_ker * (2 * (t - r) ^ (1 / 2 : ℝ)) := by
      intro r hr
      have hrp : IntervalIntegrable (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ))) volume 0 (t - r) :=
        intervalIntegrable_rpow_neg_half 0 (t - r)
      have hrp_shift : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(1 / 2 : ℝ))) volume r t := by
        have h1 := hrp.comp_sub_right r
        simpa only [zero_add, sub_add_cancel] using h1
      have hrp_Ioo : IntegrableOn (fun s : ℝ => C_ker * (s - r) ^ (-(1 / 2 : ℝ))) (Ioo r t) volume :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.2.le).1 (hrp_shift.const_mul C_ker)
      let dom_r : ℝ → ℝ := (Ioo r t).indicator (fun s => C_ker * (s - r) ^ (-(1 / 2 : ℝ)))
      have hdom_int_vol : Integrable dom_r volume :=
        (integrable_indicator_iff measurableSet_Ioo).2 hrp_Ioo
      have hdom_int : Integrable dom_r μI := hdom_int_vol.restrict
      have hG_slice_meas : AEStronglyMeasurable (fun s => G (r, s)) μI := by
        have hc_on : ContinuousOn (fun s => K r s) (Ioo r t) :=
          (hK_contOn.comp (continuous_const.prodMk continuous_id).continuousOn
            (fun s hs => ⟨hr.1, hs.1, hs.2⟩)).congr (fun _ _ => rfl)
        have h_ind : EqOn (fun s => G (r, s)) ((Ioo r t).indicator (fun s => K r s)) (Ioo 0 t) := by
          intro s hs
          by_cases hsr : r < s
          · have hp : (r, s) ∈ T_open := ⟨hr.1, hsr, hs.2⟩
            have hs' : s ∈ Ioo r t := ⟨hsr, hs.2⟩
            simp only [G, indicator_of_mem hp, indicator_of_mem hs']
          · have hp : (r, s) ∉ T_open := fun h => hsr h.2.1
            have hs' : s ∉ Ioo r t := fun h => hsr h.1
            simp only [G, indicator_of_notMem hp, indicator_of_notMem hs']
        have hm1 : AEStronglyMeasurable ((Ioo r t).indicator (fun s => K r s)) volume :=
          (aestronglyMeasurable_indicator_iff measurableSet_Ioo).2
            (hc_on.aestronglyMeasurable measurableSet_Ioo)
        exact hm1.restrict.congr (ae_restrict_of_forall_mem measurableSet_Ioo h_ind.symm)
      have hle_dom : ∀ s ∈ Ioo (0 : ℝ) t, ‖G (r, s)‖ ≤ dom_r s := by
        intro s hs
        refine (hG_bound (r, s)).trans (le_of_eq ?_)
        by_cases hsr : r < s
        · have hp : (r, s) ∈ T_open := ⟨hr.1, hsr, hs.2⟩
          have hs' : s ∈ Ioo r t := ⟨hsr, hs.2⟩
          rw [indicator_of_mem hp]
          dsimp only [dom_r]
          rw [indicator_of_mem hs']
        · have hp : (r, s) ∉ T_open := fun h => hsr h.2.1
          have hs' : s ∉ Ioo r t := fun h => hsr h.1
          rw [indicator_of_notMem hp]
          dsimp only [dom_r]
          rw [indicator_of_notMem hs']
      have hint_Gr : Integrable (fun s => G (r, s)) μI :=
        hdom_int.mono' hG_slice_meas (ae_restrict_of_forall_mem measurableSet_Ioo hle_dom)
      refine ⟨hint_Gr, ?_⟩
      calc ∫ s, ‖G (r, s)‖ ∂μI
          ≤ ∫ s, dom_r s ∂μI :=
            integral_mono_ae hint_Gr.norm hdom_int
              (ae_restrict_of_forall_mem measurableSet_Ioo hle_dom)
        _ ≤ ∫ s, dom_r s ∂volume :=
            setIntegral_le_integral hdom_int_vol (Eventually.of_forall fun s => by
              change 0 ≤ dom_r s
              by_cases hs : s ∈ Ioo r t
              · dsimp only [dom_r]
                rw [indicator_of_mem hs]
                exact mul_nonneg hC_ker_nn (Real.rpow_nonneg (sub_pos.mpr hs.1).le _)
              · dsimp only [dom_r]
                rw [indicator_of_notMem hs])
        _ = ∫ s in Ioo r t, C_ker * (s - r) ^ (-(1 / 2 : ℝ)) :=
            integral_indicator measurableSet_Ioo
        _ = C_ker * ∫ s in r..t, (s - r) ^ (-(1 / 2 : ℝ)) := by
            rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.2.le,
              intervalIntegral.integral_const_mul]
        _ = C_ker * (2 * (t - r) ^ (1 / 2 : ℝ)) := by
            have hchg := intervalIntegral.integral_comp_sub_right
              (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ))) r (a := r) (b := t)
            simp only [sub_self] at hchg
            rw [hchg, integral_rpow (Or.inl (by norm_num)),
              show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num)]
            ring
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hslice_int r hr).1
    · have hfin : IsFiniteMeasure μI := ⟨by simp [μI, Real.volume_Ioo]⟩
      refine Integrable.of_bound hG_meas_I.norm.integral_prod_right'
        (C_ker * (2 * t ^ (1 / 2 : ℝ))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      refine (hslice_int r hr).2.trans ?_
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (sub_pos.mpr hr.2).le (by linarith [hr.1]) (by norm_num))
          (by norm_num))
        hC_ker_nn
  have hfub := (MeasureTheory.integral_prod G hG_int).symm.trans
    (MeasureTheory.integral_prod_symm G hG_int)
  have hG_r : ∀ r ∈ Ioo (0 : ℝ) t, ∫ s, G (r, s) ∂μI = ∫ s in r..t, K r s := by
    intro r hr
    have hsub_Ioo : Ioo r t ⊆ Ioo 0 t := fun s hs => ⟨lt_trans hr.1 hs.1, hs.2⟩
    change ∫ s in Ioo 0 t, G (r, s) = _
    have hind_eq : ∫ s in Ioo 0 t, G (r, s) =
        ∫ s in Ioo 0 t, (Ioo r t).indicator (fun s => K r s) s := by
      refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      by_cases hsr : r < s
      · have hp : (r, s) ∈ T_open := ⟨hr.1, hsr, hs.2⟩
        have hs' : s ∈ Ioo r t := ⟨hsr, hs.2⟩
        simp only [G, indicator_of_mem hp, indicator_of_mem hs']
      · have hp : (r, s) ∉ T_open := fun h => hsr h.2.1
        have hs' : s ∉ Ioo r t := fun h => hsr h.1
        simp only [G, indicator_of_notMem hp, indicator_of_notMem hs']
    rw [hind_eq, setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right hsub_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.2.le]
  have hG_s : ∀ s ∈ Ioo (0 : ℝ) t, ∫ r, G (r, s) ∂μI = ∫ r in (0 : ℝ)..s, K r s := by
    intro s hs
    have hsub_Ioo : Ioo 0 s ⊆ Ioo 0 t := fun r hr => ⟨hr.1, lt_trans hr.2 hs.2⟩
    change ∫ r in Ioo 0 t, G (r, s) = _
    have hind_eq : ∫ r in Ioo 0 t, G (r, s) =
        ∫ r in Ioo 0 t, (Ioo 0 s).indicator (fun r => K r s) r := by
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
      by_cases hrs : r < s
      · have hp : (r, s) ∈ T_open := ⟨hr.1, hrs, hs.2⟩
        have hr' : r ∈ Ioo 0 s := ⟨hr.1, hrs⟩
        simp only [G, indicator_of_mem hp, indicator_of_mem hr']
      · have hp : (r, s) ∉ T_open := fun h => hrs h.2.1
        have hr' : r ∉ Ioo 0 s := fun h => hrs h.2
        simp only [G, indicator_of_notMem hp, indicator_of_notMem hr']
    rw [hind_eq, setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right hsub_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.1.le]
  have hint_G_right : Integrable (fun s => ∫ r, G (r, s) ∂μI) μI :=
    hG_int.integral_prod_right
  refine ⟨hint_G_right.congr (ae_restrict_of_forall_mem measurableSet_Ioo hG_s), ?_⟩
  have hL : ∫ r in Ioo 0 t, ∫ s in r..t, K r s = ∫ r, (∫ s, G (r, s) ∂μI) ∂μI :=
    setIntegral_congr_fun measurableSet_Ioo fun r hr => (hG_r r hr).symm
  have hR : ∫ s, (∫ r, G (r, s) ∂μI) ∂μI = ∫ s in Ioo 0 t, ∫ r in (0 : ℝ)..s, K r s :=
    setIntegral_congr_fun measurableSet_Ioo hG_s
  exact hL.trans (hfub.trans hR)

private lemma fubini_duh_heat {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {Φ : Plane → F8Ex.RMerid} (hsm : UnforcedLeray.Sob.IsCylSmooth c Φ)
    (b : ℝ → L2v c) (hb_cont : ContinuousOn b (Icc 0 2))
    {t : ℝ} (ht_pos : 0 < t) (ht2 : t ≤ 2) :
    let φ₀ := cylSmoothToL2 hsm
    let φq := cylSmoothToL2 (hsm.dir ((1 : ℝ), (0 : ℝ)))
    let φη := cylSmoothToL2 (hsm.dir ((0 : ℝ), (1 : ℝ)))
    let K : ℝ → ℝ → ℝ := fun r s =>
      -ν * (⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ +
        ⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ)
    Integrable (fun s => ∫ r in (0 : ℝ)..s, K r s) (volume.restrict (Ioo 0 t)) ∧
      (∫ r in (0 : ℝ)..t, ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r) - b r⟫_ℝ) =
        ∫ s in Ioo 0 t, ∫ r in (0 : ℝ)..s, K r s := by
  intro φ₀ φq φη K
  obtain ⟨Mb₀, hMb₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hb_cont
  let Mb := max Mb₀ 0
  have hMb_nn : 0 ≤ Mb := le_max_right _ _
  have hb_bdd : ∀ r ∈ Icc (0 : ℝ) 2, ‖b r‖ ≤ Mb :=
    fun r hr => (hMb₀ r hr).trans (le_max_left _ _)
  let T_open : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < t}
  have hK_contOn : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) T_open := by
    have hb_p : ContinuousOn (fun p : ℝ × ℝ => b p.1) T_open :=
      hb_cont.comp continuous_fst.continuousOn (fun p hp => ⟨hp.1.le, (hp.2.1.trans hp.2.2).le.trans ht2⟩)
    have hDj : ∀ j : Fin 2,
        ContinuousOn (fun p : ℝ × ℝ => DHeatCLM hc j (ν * (p.2 - p.1)) (b p.1)) T_open := by
      intro j
      refine continuousOn_clm_apply (K := fun p : ℝ × ℝ => DHeatCLM hc j (ν * (p.2 - p.1)))
        ?_ ?_ hb_p
      · intro e
        refine (continuousOn_DHeatCLM_apply hc j e).comp
          (continuousOn_const.mul (continuousOn_snd.sub continuousOn_fst)) ?_
        intro p hp
        exact mul_pos hν (sub_pos.mpr hp.2.1)
      · intro p₀ hp₀
        let δ := (p₀.2 - p₀.1) / 2
        have hδ : 0 < δ := half_pos (sub_pos.mpr hp₀.2.1)
        refine ⟨(2 / Real.sqrt Real.pi) * (ν ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ))), ?_⟩
        have hopen_δ : IsOpen {p : ℝ × ℝ | δ < p.2 - p.1} :=
          isOpen_lt continuous_const (continuous_snd.sub continuous_fst)
        have hmem_δ : p₀ ∈ {p : ℝ × ℝ | δ < p.2 - p.1} := half_lt_self (sub_pos.mpr hp₀.2.1)
        filter_upwards [nhdsWithin_le_nhds (hopen_δ.mem_nhds hmem_δ)] with p (hp : δ < p.2 - p.1)
        have hpos : 0 < p.2 - p.1 := lt_trans hδ hp
        refine (norm_DHeatCLM_le hc j (mul_pos hν hpos)).trans ?_
        rw [heatDivL2Coeff_eq_singular hν hpos]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hδ hp.le (by norm_num))
            (Real.rpow_nonneg hν.le _))
          (by positivity)
    exact continuousOn_const.mul
      ((continuous_const.continuousOn.inner (hDj 0)).add
        (continuous_const.continuousOn.inner (hDj 1)))
  let C_ker : ℝ := ν * (‖φq‖ + ‖φη‖) * Mb * ((2 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)))
  have hC_ker_nn : 0 ≤ C_ker := by positivity
  have hK_bdd : ∀ r s : ℝ, 0 < r → r < s → s < t → |K r s| ≤ C_ker * (s - r) ^ (-(1 / 2 : ℝ)) := by
    intro r s hr0 hrs hst
    have hsr : 0 < s - r := sub_pos.mpr hrs
    have hpos : 0 < ν * (s - r) := mul_pos hν hsr
    have hbr : ‖b r‖ ≤ Mb := hb_bdd r ⟨hr0.le, (hrs.trans hst).le.trans ht2⟩
    have hb0 : ‖⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ‖ ≤
        ‖φq‖ * (heatDivL2Coeff (ν * (s - r)) * Mb) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (norm_DHeatCLM_le hc 0 hpos) hbr (norm_nonneg _)
            (by unfold heatDivL2Coeff; positivity)))
        (norm_nonneg _))
    have hb1 : ‖⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ‖ ≤
        ‖φη‖ * (heatDivL2Coeff (ν * (s - r)) * Mb) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (norm_DHeatCLM_le hc 1 hpos) hbr (norm_nonneg _)
            (by unfold heatDivL2Coeff; positivity)))
        (norm_nonneg _))
    dsimp only [K]
    rw [abs_mul, abs_neg, abs_of_pos hν]
    have habs : |⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ +
        ⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ| ≤
        ‖⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ‖ +
          ‖⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ‖ := by
      simpa only [Real.norm_eq_abs] using abs_add_le _ _
    calc
      ν * |⟪φq, _⟫_ℝ + ⟪φη, _⟫_ℝ|
          ≤ ν * (‖φq‖ * (heatDivL2Coeff (ν * (s - r)) * Mb) +
              ‖φη‖ * (heatDivL2Coeff (ν * (s - r)) * Mb)) :=
            mul_le_mul_of_nonneg_left (habs.trans (add_le_add hb0 hb1)) hν.le
      _ = C_ker * (s - r) ^ (-(1 / 2 : ℝ)) := by
            rw [heatDivL2Coeff_eq_singular hν hsr]
            dsimp only [C_ker]
            ring
  obtain ⟨hint_K, hfub⟩ := fubini_triangle_rpow_half ht_pos hK_contOn hC_ker_nn hK_bdd
  refine ⟨hint_K, ?_⟩
  rw [intervalIntegral.integral_of_le ht_pos.le, integral_Ioc_eq_integral_Ioo, ← hfub]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  have hftc_b := (inner_centeredHeat_sub_self_eq hc hν (sub_pos.mpr hr.2).le hsm (b r)).2
  rw [hftc_b]
  have hchg := (intervalIntegral.integral_comp_sub_right
    (fun σ : ℝ => -ν * (⟪φq, DHeatCLM hc 0 (ν * σ) (b r)⟫_ℝ +
      ⟪φη, DHeatCLM hc 1 (ν * σ) (b r)⟫_ℝ)) r (a := r) (b := t)).symm
  simp only [sub_self] at hchg
  exact hchg

private lemma inner_mild_weak_eq {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) {Φ : Plane → F8Ex.RMerid} (hΦ : F8Ex.IsRealSolCylTest c Φ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    let hsm := isCylSmooth_of_solTest hΦ
    let φ₀ := cylSmoothToL2 hsm
    let φq := cylSmoothToL2 (hsm.dir ((1 : ℝ), (0 : ℝ)))
    let φη := cylSmoothToL2 (hsm.dir ((0 : ℝ), (1 : ℝ)))
    let U : ℝ → H1Sol c := fun r => E_oseen hc hν hV r 0 u₀
    let b : ℝ → L2v c := fun r => bvCLM hc hV r (U r)
    ⟪φ₀, val0CLM c (U t) - val0CLM c u₀⟫_ℝ +
      ∫ s in (0 : ℝ)..t,
        (ν * (⟪φq, dqCLM c (U s)⟫_ℝ + ⟪φη, detaCLM c (U s)⟫_ℝ) + ⟪φ₀, b s⟫_ℝ) = 0 := by
  intro hsm φ₀ φq φη U b
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · simp [U, E_oseen_self hc hν hV 0]
  have hP0_φ₀ : P0 c φ₀ = φ₀ :=
    UnforcedLeray.Cyl.P0_eq_self (cylSmoothToL2_mem_divFree_of_solTest hc hΦ)
  have hP0_φq : P0 c φq = φq := by
    have hdir0 := isRealSolCylTest_dir hΦ 0
    have heq : φq = cylSmoothToL2 (isCylSmooth_of_solTest hdir0) := rfl
    rw [heq]
    exact UnforcedLeray.Cyl.P0_eq_self (cylSmoothToL2_mem_divFree_of_solTest hc hdir0)
  have hP0_φη : P0 c φη = φη := by
    have hdir1 := isRealSolCylTest_dir hΦ 1
    have heq : φη = cylSmoothToL2 (isCylSmooth_of_solTest hdir1) := rfl
    rw [heq]
    exact UnforcedLeray.Cyl.P0_eq_self (cylSmoothToL2_mem_divFree_of_solTest hc hdir1)
  have hU_cont : ContinuousOn U (Icc 0 2) :=
    continuousOn_E_oseen hc hν hV ⟨le_rfl, by norm_num⟩ u₀
  have hb_cont : ContinuousOn b (Icc 0 2) :=
    continuousOn_clm_apply (fun p => (continuous_bvCLM_apply hc hV p).continuousOn)
      (fun _ _ => ⟨6 * driftBound hV, Eventually.of_forall fun r => norm_bvCLM_le hc hV r⟩)
      hU_cont
  -- Step 1: Pair mild equation for `val0CLM c (U t)` with `φ₀`
  obtain ⟨hint_t, hmild_t⟩ := E_oseen_mild hc hν hV le_rfl ht.1 ht.2 u₀
  have hval_t : val0CLM c (U t) = centeredHeatVecL2CLM hc (ν * t) (val0CLM c u₀) -
      ∫ r in (0 : ℝ)..t, P0 c (centeredHeatVecL2CLM hc (ν * (t - r)) (b r)) := by
    have hv := congrArg (val0CLM c) hmild_t
    rw [map_sub, sub_zero, val0_freeH1CLM, ← (val0CLM c).intervalIntegral_comp_comm hint_t] at hv
    rw [hv]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real t] with r hrt hr
    rw [uIoc_of_le ht.1] at hr
    have hpos : 0 < ν * (t - r) := mul_pos hν (sub_pos.mpr (lt_of_le_of_ne hr.2 hrt))
    exact val0_duhH1CLM_of_pos hc hpos (b r)
  have hint_P0H : IntervalIntegrable
      (fun r => P0 c (centeredHeatVecL2CLM hc (ν * (t - r)) (b r))) volume 0 t := by
    have h1 := clm_intervalIntegrable (val0CLM c) hint_t
    refine h1.congr_ae ?_
    rw [uIoc_of_le ht.1]
    filter_upwards [ae_restrict_of_ae (ae_ne_real t), ae_restrict_mem measurableSet_Ioc]
      with r hrt hr
    have hpos : 0 < ν * (t - r) := mul_pos hν (sub_pos.mpr (lt_of_le_of_ne hr.2 hrt))
    exact val0_duhH1CLM_of_pos hc hpos (b r)
  have hpair_duh : ⟪φ₀, ∫ r in (0 : ℝ)..t, P0 c (centeredHeatVecL2CLM hc (ν * (t - r)) (b r))⟫_ℝ =
      ∫ r in (0 : ℝ)..t, ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r)⟫_ℝ := by
    have hc1 := (innerSL ℝ φ₀).intervalIntegral_comp_comm hint_P0H
    simp only [innerSL_apply_apply] at hc1
    rw [← hc1]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [real_inner_comm, UnforcedLeray.Cyl.inner_P0_comm, hP0_φ₀, real_inner_comm]
  have hint_Hb : IntervalIntegrable
      (fun r => ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r)⟫_ℝ) volume 0 t := by
    have hc1 := clm_intervalIntegrable (innerSL ℝ φ₀) hint_P0H
    refine hc1.congr fun r _ => ?_
    simp only [innerSL_apply_apply]
    rw [real_inner_comm, UnforcedLeray.Cyl.inner_P0_comm, hP0_φ₀, real_inner_comm]
  have hint_b0 : IntervalIntegrable (fun r => ⟪φ₀, b r⟫_ℝ) volume 0 t :=
    ((continuous_const.continuousOn.inner (hb_cont.mono (Icc_subset_Icc_right ht.2)))).intervalIntegrable_of_Icc ht.1
  have hint_sub : IntervalIntegrable
      (fun r => ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r) - b r⟫_ℝ) volume 0 t := by
    simpa only [inner_sub_right] using hint_Hb.sub hint_b0
  have hsplit_t : ⟪φ₀, val0CLM c (U t) - val0CLM c u₀⟫_ℝ =
      ⟪φ₀, centeredHeatVecL2CLM hc (ν * t) (val0CLM c u₀) - val0CLM c u₀⟫_ℝ -
        (∫ r in (0 : ℝ)..t, ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r) - b r⟫_ℝ) -
        (∫ r in (0 : ℝ)..t, ⟪φ₀, b r⟫_ℝ) := by
    have h1 : val0CLM c (U t) - val0CLM c u₀ =
        (centeredHeatVecL2CLM hc (ν * t) (val0CLM c u₀) - val0CLM c u₀) -
          ∫ r in (0 : ℝ)..t, P0 c (centeredHeatVecL2CLM hc (ν * (t - r)) (b r)) := by
      rw [hval_t]; abel
    rw [h1, inner_sub_right, hpair_duh]
    have h2 : (∫ r in (0 : ℝ)..t, ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r)⟫_ℝ) =
        (∫ r in (0 : ℝ)..t, ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r) - b r⟫_ℝ) +
          (∫ r in (0 : ℝ)..t, ⟪φ₀, b r⟫_ℝ) := by
      rw [← intervalIntegral.integral_add hint_sub hint_b0]
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [inner_sub_right, sub_add_cancel]
    linarith
  -- Step 2: Free term FTC
  have hftc_free := (inner_centeredHeat_sub_self_eq hc hν ht.1 hsm (val0CLM c u₀)).2
  have hfree_eq : ⟪φ₀, centeredHeatVecL2CLM hc (ν * t) (val0CLM c u₀) - val0CLM c u₀⟫_ℝ =
      ∫ s in (0 : ℝ)..t, -ν * (⟪φq, centeredHeatVecL2CLM hc (ν * s) (dqCLM c u₀)⟫_ℝ +
        ⟪φη, centeredHeatVecL2CLM hc (ν * s) (detaCLM c u₀)⟫_ℝ) := by
    rw [hftc_free]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real 0] with s hs0 hs
    rw [uIoc_of_le ht.1] at hs
    have hpos : 0 < ν * s := mul_pos hν hs.1
    rw [DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_q u₀),
      DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_eta u₀)]
  -- Step 3: Fubini exchange via `fubini_duh_heat` + slice mild eq
  obtain ⟨hint_K_right, hfub_duh⟩ := fubini_duh_heat hc hν hsm b hb_cont ht_pos ht.2
  let K : ℝ → ℝ → ℝ := fun r s =>
    -ν * (⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ +
      ⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ)
  have hR_slice : ∀ s ∈ Ioo (0 : ℝ) t,
      (-ν * (⟪φq, centeredHeatVecL2CLM hc (ν * s) (dqCLM c u₀)⟫_ℝ +
          ⟪φη, centeredHeatVecL2CLM hc (ν * s) (detaCLM c u₀)⟫_ℝ)) -
        (∫ r in (0 : ℝ)..s, K r s) =
      -ν * (⟪φq, dqCLM c (U s)⟫_ℝ + ⟪φη, detaCLM c (U s)⟫_ℝ) := by
    intro s hs
    have hs2 : s ≤ 2 := hs.2.le.trans ht.2
    obtain ⟨hint_s, hmild_s⟩ := E_oseen_mild hc hν hV le_rfl hs.1.le hs2 u₀
    have hdq_s : dqCLM c (U s) = centeredHeatVecL2CLM hc (ν * s) (dqCLM c u₀) -
        ∫ r in (0 : ℝ)..s, P0 c (DHeatCLM hc 0 (ν * (s - r)) (b r)) := by
      have hv := congrArg (dqCLM c) hmild_s
      rw [map_sub, sub_zero, dq_freeH1CLM, ← (dqCLM c).intervalIntegral_comp_comm hint_s] at hv
      rw [hv]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_real s] with r hrs hr
      rw [uIoc_of_le hs.1.le] at hr
      have hpos : 0 < ν * (s - r) := mul_pos hν (sub_pos.mpr (lt_of_le_of_ne hr.2 hrs))
      exact dq_duhH1CLM_of_pos hc hpos (b r)
    have hdeta_s : detaCLM c (U s) = centeredHeatVecL2CLM hc (ν * s) (detaCLM c u₀) -
        ∫ r in (0 : ℝ)..s, P0 c (DHeatCLM hc 1 (ν * (s - r)) (b r)) := by
      have hv := congrArg (detaCLM c) hmild_s
      rw [map_sub, sub_zero, deta_freeH1CLM, ← (detaCLM c).intervalIntegral_comp_comm hint_s] at hv
      rw [hv]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_real s] with r hrs hr
      rw [uIoc_of_le hs.1.le] at hr
      have hpos : 0 < ν * (s - r) := mul_pos hν (sub_pos.mpr (lt_of_le_of_ne hr.2 hrs))
      exact deta_duhH1CLM_of_pos hc hpos (b r)
    have hint_D0 : IntervalIntegrable
        (fun r => P0 c (DHeatCLM hc 0 (ν * (s - r)) (b r))) volume 0 s := by
      have h1 := clm_intervalIntegrable (dqCLM c) hint_s
      refine h1.congr_ae ?_
      rw [uIoc_of_le hs.1.le]
      filter_upwards [ae_restrict_of_ae (ae_ne_real s), ae_restrict_mem measurableSet_Ioc]
        with r hrs hr
      have hpos : 0 < ν * (s - r) := mul_pos hν (sub_pos.mpr (lt_of_le_of_ne hr.2 hrs))
      exact dq_duhH1CLM_of_pos hc hpos (b r)
    have hint_D1 : IntervalIntegrable
        (fun r => P0 c (DHeatCLM hc 1 (ν * (s - r)) (b r))) volume 0 s := by
      have h1 := clm_intervalIntegrable (detaCLM c) hint_s
      refine h1.congr_ae ?_
      rw [uIoc_of_le hs.1.le]
      filter_upwards [ae_restrict_of_ae (ae_ne_real s), ae_restrict_mem measurableSet_Ioc]
        with r hrs hr
      have hpos : 0 < ν * (s - r) := mul_pos hν (sub_pos.mpr (lt_of_le_of_ne hr.2 hrs))
      exact deta_duhH1CLM_of_pos hc hpos (b r)
    have hpair_q : ⟪φq, ∫ r in (0 : ℝ)..s, P0 c (DHeatCLM hc 0 (ν * (s - r)) (b r))⟫_ℝ =
        ∫ r in (0 : ℝ)..s, ⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ := by
      have hc1 := (innerSL ℝ φq).intervalIntegral_comp_comm hint_D0
      simp only [innerSL_apply_apply] at hc1
      rw [← hc1]
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [real_inner_comm, UnforcedLeray.Cyl.inner_P0_comm, hP0_φq, real_inner_comm]
    have hpair_η : ⟪φη, ∫ r in (0 : ℝ)..s, P0 c (DHeatCLM hc 1 (ν * (s - r)) (b r))⟫_ℝ =
        ∫ r in (0 : ℝ)..s, ⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ := by
      have hc1 := (innerSL ℝ φη).intervalIntegral_comp_comm hint_D1
      simp only [innerSL_apply_apply] at hc1
      rw [← hc1]
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [real_inner_comm, UnforcedLeray.Cyl.inner_P0_comm, hP0_φη, real_inner_comm]
    have hi_q : IntervalIntegrable
        (fun r => ⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ) volume 0 s := by
      refine (clm_intervalIntegrable (innerSL ℝ φq) hint_D0).congr fun r _ => ?_
      simp only [innerSL_apply_apply]
      rw [real_inner_comm, UnforcedLeray.Cyl.inner_P0_comm, hP0_φq, real_inner_comm]
    have hi_η : IntervalIntegrable
        (fun r => ⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ) volume 0 s := by
      refine (clm_intervalIntegrable (innerSL ℝ φη) hint_D1).congr fun r _ => ?_
      simp only [innerSL_apply_apply]
      rw [real_inner_comm, UnforcedLeray.Cyl.inner_P0_comm, hP0_φη, real_inner_comm]
    have hK_int : ∫ r in (0 : ℝ)..s, K r s =
        -ν * ((∫ r in (0 : ℝ)..s, ⟪φq, DHeatCLM hc 0 (ν * (s - r)) (b r)⟫_ℝ) +
          (∫ r in (0 : ℝ)..s, ⟪φη, DHeatCLM hc 1 (ν * (s - r)) (b r)⟫_ℝ)) := by
      dsimp only [K]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi_q hi_η]
    rw [hK_int, hdq_s, hdeta_s, inner_sub_right, inner_sub_right, hpair_q, hpair_η]
    ring
  -- Step 4: Combine everything on `0..t`
  have hint_free_Ioo : Integrable (fun s => -ν * (⟪φq, centeredHeatVecL2CLM hc (ν * s) (dqCLM c u₀)⟫_ℝ +
      ⟪φη, centeredHeatVecL2CLM hc (ν * s) (detaCLM c u₀)⟫_ℝ)) (volume.restrict (Ioo 0 t)) := by
    have hcont : Continuous (fun s => -ν * (⟪φq, centeredHeatVecL2CLM hc (ν * s) (dqCLM c u₀)⟫_ℝ +
        ⟪φη, centeredHeatVecL2CLM hc (ν * s) (detaCLM c u₀)⟫_ℝ)) :=
      continuous_const.mul
        ((continuous_const.inner ((continuous_centeredHeatVecL2CLM_apply hc _).comp
            (continuous_const.mul continuous_id))).add
          (continuous_const.inner ((continuous_centeredHeatVecL2CLM_apply hc _).comp
            (continuous_const.mul continuous_id))))
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).1
      (hcont.intervalIntegrable 0 t)
  have hvisc_comb :
      ⟪φ₀, centeredHeatVecL2CLM hc (ν * t) (val0CLM c u₀) - val0CLM c u₀⟫_ℝ -
        (∫ r in (0 : ℝ)..t, ⟪φ₀, centeredHeatVecL2CLM hc (ν * (t - r)) (b r) - b r⟫_ℝ) =
      ∫ s in (0 : ℝ)..t, -ν * (⟪φq, dqCLM c (U s)⟫_ℝ + ⟪φη, detaCLM c (U s)⟫_ℝ) := by
    rw [hfree_eq, hfub_duh, intervalIntegral.integral_of_le ht.1,
      integral_Ioc_eq_integral_Ioo]
    rw [← integral_sub hint_free_Ioo hint_K_right, intervalIntegral.integral_of_le ht.1,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo hR_slice
  have hint_visc : IntervalIntegrable
      (fun s => ν * (⟪φq, dqCLM c (U s)⟫_ℝ + ⟪φη, detaCLM c (U s)⟫_ℝ)) volume 0 t := by
    have hc_on : ContinuousOn
        (fun s => ν * (⟪φq, dqCLM c (U s)⟫_ℝ + ⟪φη, detaCLM c (U s)⟫_ℝ)) (Icc 0 t) :=
      continuousOn_const.mul
        ((continuous_const.continuousOn.inner ((dqCLM c).continuous.comp_continuousOn
            (hU_cont.mono (Icc_subset_Icc_right ht.2)))).add
          (continuous_const.continuousOn.inner ((detaCLM c).continuous.comp_continuousOn
            (hU_cont.mono (Icc_subset_Icc_right ht.2)))))
    exact hc_on.intervalIntegrable_of_Icc ht.1
  have hneg : (∫ s in (0 : ℝ)..t, -ν * (⟪φq, dqCLM c (U s)⟫_ℝ + ⟪φη, detaCLM c (U s)⟫_ℝ)) =
      -(∫ s in (0 : ℝ)..t, ν * (⟪φq, dqCLM c (U s)⟫_ℝ + ⟪φη, detaCLM c (U s)⟫_ℝ)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => by ring
  have hadd_int := intervalIntegral.integral_add hint_visc hint_b0
  linarith [hsplit_t, hvisc_comb, hneg, hadd_int]

/-! ## 6. Canonical mild-weak `C([0, 2]; H¹_σ(C_c))` solution and `RealCylOseenWeakH1Exists` -/

private lemma eLpNorm_cellMeas_eq_ofReal_norm {c : ℝ} {f : Plane → F8Ex.RMerid} {x : L2v c}
    (hae : f =ᵐ[F8Ex.cellMeas c] (x : Plane → F8Ex.RMerid)) :
    F8Ex.cellL2R c f = ENNReal.ofReal ‖x‖ := by
  unfold F8Ex.cellL2R
  rw [eLpNorm_congr_ae hae]
  have h1 : eLpNorm (x : Plane → F8Ex.RMerid) 2 (F8Ex.cellMeas c) =
      eLpNorm (x : Plane → Vec2) 2 (cellμ c) := by
    let g : Plane → Vec2 := x
    change eLpNorm g 2 (F8Ex.cellMeas c) = eLpNorm g 2 (cellμ c)
    rw [cellMeas_eq_cellμ]
  rw [h1, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top x)]

theorem exists_mild_weakH1OseenSol {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    {u uq uη : Plane → F8Ex.RMerid} (hdat : F8Ex.IsRealCylH1Datum c u uq uη) :
    let u₀ := H1Sol.ofRealDatum hdat
    let U : ℝ → H1Sol c := fun s => E_oseen hc hν hV s 0 u₀
    let W : ℝ → Plane → F8Ex.RMerid := fun s => if s = 0 then u else (val0CLM c (U s) : Plane → F8Ex.RMerid)
    let Wq : ℝ → Plane → F8Ex.RMerid := fun s => if s = 0 then uq else (dqCLM c (U s) : Plane → F8Ex.RMerid)
    let Wη : ℝ → Plane → F8Ex.RMerid := fun s => if s = 0 then uη else (detaCLM c (U s) : Plane → F8Ex.RMerid)
    F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη ∧
    (∀ s ∈ Icc (0 : ℝ) 2,
      W s =ᵐ[F8Ex.cellMeas c] (val0CLM c (U s) : Plane → F8Ex.RMerid) ∧
      Wq s =ᵐ[F8Ex.cellMeas c] (dqCLM c (U s) : Plane → F8Ex.RMerid) ∧
      Wη s =ᵐ[F8Ex.cellMeas c] (detaCLM c (U s) : Plane → F8Ex.RMerid)) := by
  intro u₀ U W Wq Wη
  have hU0 : U 0 = u₀ := by simp [U, E_oseen_self hc hν hV 0]
  obtain ⟨hu0, huq, huη⟩ := H1Sol.ofRealDatum_ae hdat
  have hae_all : ∀ s ∈ Icc (0 : ℝ) 2,
      W s =ᵐ[F8Ex.cellMeas c] (val0CLM c (U s) : Plane → F8Ex.RMerid) ∧
      Wq s =ᵐ[F8Ex.cellMeas c] (dqCLM c (U s) : Plane → F8Ex.RMerid) ∧
      Wη s =ᵐ[F8Ex.cellMeas c] (detaCLM c (U s) : Plane → F8Ex.RMerid) := by
    intro s _
    by_cases hs0 : s = 0
    · subst hs0
      simp only [W, Wq, Wη, ↓reduceIte, hU0]
      exact ⟨hu0.symm, huq.symm, huη.symm⟩
    · simp [W, Wq, Wη, hs0]
  refine ⟨?_, hae_all⟩
  refine
    { slice_h1 := fun s _ => by
        by_cases hs0 : s = 0
        · subst hs0; simpa [W, Wq, Wη] using hdat
        · simpa [W, Wq, Wη, hs0] using H1Sol.isRealCylH1Datum (U s)
      init_eq := by simp [W, Wq, Wη]
      cont_h1 := fun s hs => ?_
      weak_eq := fun Φ hΦ t ht => ?_ }
  · have hU_cont : ContinuousOn U (Icc 0 2) :=
      continuousOn_E_oseen hc hν hV ⟨le_rfl, by norm_num⟩ u₀
    have hlimU : Tendsto U (𝓝[Icc 0 2] s) (𝓝 (U s)) := hU_cont s hs
    have hlim0 : Tendsto (fun t => ENNReal.ofReal ‖val0CLM c (U t) - val0CLM c (U s)‖)
        (𝓝[Icc 0 2] s) (𝓝 0) := by
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.1 (((val0CLM c).continuous.tendsto (U s)).comp hlimU))
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
    have hlimq : Tendsto (fun t => ENNReal.ofReal ‖dqCLM c (U t) - dqCLM c (U s)‖)
        (𝓝[Icc 0 2] s) (𝓝 0) := by
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.1 (((dqCLM c).continuous.tendsto (U s)).comp hlimU))
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
    have hlimη : Tendsto (fun t => ENNReal.ofReal ‖detaCLM c (U t) - detaCLM c (U s)‖)
        (𝓝[Icc 0 2] s) (𝓝 0) := by
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.1 (((detaCLM c).continuous.tendsto (U s)).comp hlimU))
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
    have hsum : Tendsto (fun t =>
        ENNReal.ofReal ‖val0CLM c (U t) - val0CLM c (U s)‖ +
          ENNReal.ofReal ‖dqCLM c (U t) - dqCLM c (U s)‖ +
          ENNReal.ofReal ‖detaCLM c (U t) - detaCLM c (U s)‖)
        (𝓝[Icc 0 2] s) (𝓝 0) := by
      simpa using (hlim0.add hlimq).add hlimη
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨ht0, htq, htη⟩ := hae_all t ht
    obtain ⟨hs0, hsq, hsη⟩ := hae_all s hs
    have sub_ae : ∀ (f₁ f₂ : Plane → F8Ex.RMerid) (x₁ x₂ : L2v c),
        f₁ =ᵐ[F8Ex.cellMeas c] (x₁ : Plane → F8Ex.RMerid) →
        f₂ =ᵐ[F8Ex.cellMeas c] (x₂ : Plane → F8Ex.RMerid) →
        (fun y => f₁ y - f₂ y) =ᵐ[F8Ex.cellMeas c] ((x₁ - x₂ : L2v c) : Plane → F8Ex.RMerid) := by
      intro f₁ f₂ x₁ x₂ h1 h2
      have hsub := ae_cellMeas_of_ae_cellμ (Lp.coeFn_sub x₁ x₂)
      filter_upwards [h1, h2, hsub] with y a1 a2 asub
      rw [a1, a2, asub, Pi.sub_apply]
    dsimp only [F8Ex.cylH1R]
    rw [eLpNorm_cellMeas_eq_ofReal_norm (sub_ae _ _ _ _ ht0 hs0),
      eLpNorm_cellMeas_eq_ofReal_norm (sub_ae _ _ _ _ htq hsq),
      eLpNorm_cellMeas_eq_ofReal_norm (sub_ae _ _ _ _ htη hsη)]
  · let hsm := isCylSmooth_of_solTest hΦ
    let φ₀ := cylSmoothToL2 hsm
    let φq := cylSmoothToL2 (hsm.dir (B0579.dir 0))
    let φη := cylSmoothToL2 (hsm.dir (B0579.dir 1))
    let b : ℝ → L2v c := fun r => bvCLM hc hV r (U r)
    have hU_cont : ContinuousOn U (Icc 0 2) :=
      continuousOn_E_oseen hc hν hV ⟨le_rfl, by norm_num⟩ u₀
    have hb_cont : ContinuousOn b (Icc 0 2) :=
      continuousOn_clm_apply (fun p => (continuous_bvCLM_apply hc hV p).continuousOn)
        (fun _ _ => ⟨6 * driftBound hV, Eventually.of_forall fun r => norm_bvCLM_le hc hV r⟩)
        hU_cont
    let F_l2 : ℝ → ℝ := fun r =>
      ν * (⟪φq, dqCLM c (U r)⟫_ℝ + ⟪φη, detaCLM c (U r)⟫_ℝ) + ⟪φ₀, b r⟫_ℝ
    have hF_l2_cont : ContinuousOn F_l2 (Icc 0 2) :=
      (continuousOn_const.mul
        ((continuous_const.continuousOn.inner ((dqCLM c).continuous.comp_continuousOn hU_cont)).add
          (continuous_const.continuousOn.inner ((detaCLM c).continuous.comp_continuousOn hU_cont)))).add
        (continuous_const.continuousOn.inner hb_cont)
    have hint_l2 : IntervalIntegrable F_l2 volume 0 t :=
      (hF_l2_cont.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hslice_eq : ∀ r ∈ Icc (0 : ℝ) 2,
        (∫ y in B0579.cell c,
          (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
              B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
            inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))) = F_l2 r := by
      intro r hr
      obtain ⟨hr0, hrq, hrη⟩ := hae_all r hr
      have hbv_ae : F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) =ᵐ[F8Ex.cellMeas c]
          (b r : Plane → F8Ex.RMerid) := by
        filter_upwards [hr0, hrq, hrη, bvCLM_ae_realBvSlice hc hV hr (U r)] with y a0 aq aη abv
        rw [abv]
        simp only [F8Ex.realBvSlice, a0, aq, aη]
      have hq_int : ⟪φq, dqCLM c (U r)⟫_ℝ =
          ∫ y in B0579.cell c, ∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k := by
        rw [inner_cylSmoothToL2_right]
        refine integral_congr_ae ?_
        filter_upwards [hrq] with y aq
        rw [← aq, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
          pd_coord_cylSmooth hsm 0 0 y, pd_coord_cylSmooth hsm 0 1 y]
        simp [mul_comm]
      have hη_int : ⟪φη, detaCLM c (U r)⟫_ℝ =
          ∫ y in B0579.cell c, ∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k := by
        rw [inner_cylSmoothToL2_right]
        refine integral_congr_ae ?_
        filter_upwards [hrη] with y aη
        rw [← aη, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
          pd_coord_cylSmooth hsm 1 0 y, pd_coord_cylSmooth hsm 1 1 y]
        simp [mul_comm]
      have hb_int : ⟪φ₀, b r⟫_ℝ =
          ∫ y in B0579.cell c, inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y) := by
        rw [inner_cylSmoothToL2_right]
        refine integral_congr_ae ?_
        filter_upwards [hbv_ae] with y abv
        rw [abv]
      have hmΦ : MemLp Φ 2 (F8Ex.cellMeas c) := F8Ex.memLp_realSolCylTest hΦ
      have hmb : MemLp (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r)) 2 (F8Ex.cellMeas c) := by
        have hmb0 : MemLp (b r : Plane → F8Ex.RMerid) 2 (F8Ex.cellMeas c) := by
          let gb : Plane → Vec2 := b r
          change MemLp gb 2 (F8Ex.cellMeas c)
          rw [cellMeas_eq_cellμ]
          exact Lp.memLp (b r)
        exact MemLp.ae_eq hbv_ae.symm hmb0
      have hi_bv : IntegrableOn
          (fun y => inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))
          (B0579.cell c) volume := F8Ex.integrableOn_innerR_cell hmΦ hmb
      have hi_q : IntegrableOn
          (fun y => ∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k)
          (B0579.cell c) volume := by
        have hi0 : IntegrableOn
            (fun y => ⟪fderiv ℝ Φ y (B0579.dir 0), (dqCLM c (U r) : Plane → F8Ex.RMerid) y⟫_ℝ)
            (B0579.cell c) volume := by
          rw [b0579_cell_eq_cyl_cell]
          refine (L2.integrable_inner (𝕜 := ℝ) φq (dqCLM c (U r))).congr ?_
          filter_upwards [(memLp_of_cylSmooth (hsm.dir (B0579.dir 0))).coeFn_toLp] with y hy
          dsimp only [φq, cylSmoothToL2]
          rw [hy]
        refine hi0.congr ?_
        filter_upwards [hrq] with y aq
        rw [← aq, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
          pd_coord_cylSmooth hsm 0 0 y, pd_coord_cylSmooth hsm 0 1 y]
        simp [mul_comm]
      have hi_η : IntegrableOn
          (fun y => ∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k)
          (B0579.cell c) volume := by
        have hi1 : IntegrableOn
            (fun y => ⟪fderiv ℝ Φ y (B0579.dir 1), (detaCLM c (U r) : Plane → F8Ex.RMerid) y⟫_ℝ)
            (B0579.cell c) volume := by
          rw [b0579_cell_eq_cyl_cell]
          refine (L2.integrable_inner (𝕜 := ℝ) φη (detaCLM c (U r))).congr ?_
          filter_upwards [(memLp_of_cylSmooth (hsm.dir (B0579.dir 1))).coeFn_toLp] with y hy
          dsimp only [φη, cylSmoothToL2]
          rw [hy]
        refine hi1.congr ?_
        filter_upwards [hrη] with y aη
        rw [← aη, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
          pd_coord_cylSmooth hsm 1 0 y, pd_coord_cylSmooth hsm 1 1 y]
        simp [mul_comm]
      have hsplit_sum :
          (∫ y in B0579.cell c,
            (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
                B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
              inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))) =
          (∫ y in B0579.cell c,
            (ν * ((∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k) +
                (∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
              inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))) := by
        refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => ?_
        simp only [Fin.sum_univ_two]
        ring
      have hi_visc : IntegrableOn
          (fun y => ν * ((∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k) +
              (∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k)))
          (B0579.cell c) volume :=
        (Integrable.add hi_q hi_η).const_mul ν
      rw [hsplit_sum, integral_add hi_visc hi_bv, integral_const_mul, integral_add hi_q hi_η,
        ← hq_int, ← hη_int, ← hb_int]
    have huIcc : ∀ r ∈ uIcc 0 t, r ∈ Icc (0 : ℝ) 2 := by
      rw [uIcc_of_le ht.1]
      exact fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
    have hint_wk : IntervalIntegrable
        (fun r => ∫ y in B0579.cell c,
          (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
              B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
            inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))) volume 0 t :=
      hint_l2.congr fun r hr => (hslice_eq r (huIcc r (uIoc_subset_uIcc hr))).symm
    have hhead : (∫ y in B0579.cell c, inner ℝ (Φ y) (W t y - u y)) =
        ⟪φ₀, val0CLM c (U t) - val0CLM c u₀⟫_ℝ := by
      rw [inner_cylSmoothToL2_right]
      obtain ⟨ht0, _, _⟩ := hae_all t ht
      have hsub := ae_cellMeas_of_ae_cellμ (Lp.coeFn_sub (val0CLM c (U t)) (val0CLM c u₀))
      refine integral_congr_ae ?_
      filter_upwards [ht0, hu0, hsub] with y a1 a2 asub
      have hdiff : W t y - u y = ((val0CLM c (U t) - val0CLM c u₀ : L2v c) : Plane → Vec2) y := by
        dsimp only [u₀] at asub ⊢
        rw [a1, ← a2, asub, Pi.sub_apply]
      rw [hdiff]
    refine ⟨hint_wk, ?_⟩
    rw [hhead, intervalIntegral.integral_congr (fun r hr => hslice_eq r (huIcc r hr))]
    exact inner_mild_weak_eq hc hν hV u₀ hΦ ht

theorem realCylOseenWeakH1Exists : RealCylOseenWeakH1Exists := by
  intro c ν hc hν V hV u uq uη hdat
  obtain ⟨hwk, _⟩ := exists_mild_weakH1OseenSol hc hν hV hdat
  exact ⟨_, _, _, hwk⟩

end UnforcedLeray.Short.IIb.F8WeakEx
