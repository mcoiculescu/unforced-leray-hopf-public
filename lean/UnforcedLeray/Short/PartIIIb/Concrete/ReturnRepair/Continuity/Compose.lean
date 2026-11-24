import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.AMu

/-!
# Operator-norm continuity on the concrete return sequence: the reduction to the leaves
(source 5684-5685, 5701-5704, 5785-5833, 5918-5920)

Source of record: `the November 2 reference manuscript` (73 pages).

"Continuity follows from the resolvent identity, the dominated separated dilation kernels and the
polynomial near inverse; the products and finite conormal affine construction are continuous"
(5701-5704).  This file proves the "products" part: where the near layer is invertible
(`NearAt`), the return operators of the regime are `ReturnBase.toOps` of the pinned base
(`concreteOps_eq`), so (source 5790-5818)

* `𝒫 = 𝒥 R_μ F_A`, `𝒬 = -𝒥 v_Q Tc`, `L = 𝓛 Tc`, `a_μ`, `Λ_{μ,ν}` are the pinned fields;
* `𝒥 v = (D_N⁻¹Mv, v - S_N D_N⁻¹Mv)` lands in `𝓔_ν`, whose pair norm is induced by the isometric
  embedding `(T, w) ↦ (T, e^{-γ/(8ν)}w)` (`PairSp.embLI`), so a family into `𝓔_ν` is continuous iff
  its embedded family is (`PairSp.continuousOn_iff_embCLM`); the embedded `𝒥` is `jliftEOf`, a
  product of the primary operators;
* `S_N = SNop` and `D_N⁻¹ = DNinvG` are fixed transports of the near operator `S_N : Z → H`, and
  `D_N = I + M_US_N` is a unit on the window, so `D_N⁻¹` is continuous with `S_N` (`Ring.inverse`
  is continuous at units of the Banach algebra `Z →L Z`: "the polynomial near inverse", 5703).

Main statements:

* `normContinuousAt_of` : at one level, `NormContinuousAt` from the invertibility of the near layer
  on `[-1,1]` and the continuity on the window `μ_n([-1,1])` of `Sop`, `Rop`, the Ward fields
  `Y, Ẽ`, the near operator `S_N`, `𝓛`, `F_A`, `E_A`, `𝔯_A`, `a_μ`, `Λ`;
* **`returnNormContinuity_concrete_of`** : `ConcreteReturnNormContinuity D G` from the leaves of
  `Continuity/Defs.lean` and `NearAt` on the window for large `n`;
* **`returnNormContinuity_concrete_of_standing`** : the same from `SeqData.RepairStanding`
  (which supplies `NearAt`, field `near`) and the leaves other than `AMuCont`
  (`SeqData.aMuCont`, `Continuity/AMu.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Continuity into the pair space `𝓔_ν` -/

namespace PairSp

variable {V S : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup S] [NormedSpace ℝ S] {M : V →L[ℝ] S} {a ν : ℝ}

/-- The embedding `(T, w) ↦ (T, e^{-a/ν}w)` as a linear isometry (the pair norm of `𝓔_ν` is
induced by it, source 5658). -/
def embLI : PairSp M a ν →ₗᵢ[ℝ] WithLp 1 (S × V) :=
  { embL M a ν with norm_map' := fun _ => rfl }

/-- **A family of operators into `𝓔_ν` is norm continuous iff its embedded family is.** -/
theorem continuousOn_iff_embCLM {X Y : Type} [TopologicalSpace X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {f : X → Y →L[ℝ] PairSp M a ν} {s : Set X} :
    ContinuousOn f s ↔ ContinuousOn (fun x => (embCLM : PairSp M a ν →L[ℝ] _).comp (f x)) s := by
  have hI : Topology.IsInducing (((embLI (M := M) (a := a) (ν := ν)).postcomp :
      (Y →L[ℝ] PairSp M a ν) →ₗᵢ[ℝ] (Y →L[ℝ] WithLp 1 (S × V))) :
      (Y →L[ℝ] PairSp M a ν) → (Y →L[ℝ] WithLp 1 (S × V))) :=
    (LinearIsometry.isEmbedding _).isInducing
  rw [hI.continuousOn_iff]
  rfl

end PairSp

/-- `𝒥` read through the embedding is `jliftE` (source 5790-5793). -/
theorem embCLM_comp_jlift {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) :
    PairSp.embCLM.comp B.jlift = B.jliftE := by
  ext1 v
  rfl

/-! ## 2. The return operators of the regime from the primary operators -/

section Formulas

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- The embedded near graph lift `v ↦ (D(Mv), e^{-γ/(8ν)}(v - S D(Mv)))` with given `D`, `S`
(source 5790-5793; `ReturnBase.jliftE` with `M = multOp`). -/
def jliftEOf (Dinv : LStr Pl K L →L[ℝ] LStr Pl K L) (SN : LStr Pl K L →L[ℝ] LVel Pl L) :
    LVel Pl L →L[ℝ] WithLp 1 (LStr Pl K L × LVel Pl L) :=
  ((WithLp.prodContinuousLinearEquiv 1 ℝ (LStr Pl K L) (LVel Pl L)).symm :
      LStr Pl K L × LVel Pl L →L[ℝ] WithLp 1 (LStr Pl K L × LVel Pl L)).comp
    ((Dinv.comp (multOp Pl K L)).prod
      (Real.exp (-(gRate Pl / 8) / L.ν) •
        (ContinuousLinearMap.id ℝ (LVel Pl L) - SN.comp (Dinv.comp (multOp Pl K L)))))

/-- The error velocity `v_Q = (S_μ - S_N) + Y + R_μ(Ẽ - E_{𝓛} - 𝔯_{𝓛})` from the primary
operators (source 5807, `ReturnBase.vQL`). -/
def vQOf (μ : ℝ) : LStr Pl K L →L[ℝ] LVel Pl L :=
  (Sop Pl K L μ - SNop Pl K L μ) + (wardOps Pl K L μ).1 +
    (Rop Pl L μ).comp ((wardOps Pl K L μ).2.2 - (EAOp K L μ).comp (LjOp Pl K L μ) -
      (rAOp Pl K L μ).comp (LjOp Pl K L μ))

/-- `𝒫 = 𝒥R_μF_A` (source 5815-5816), read through the embedding of `𝓔_ν`. -/
theorem concreteOps_embP (μ : ℝ) (h : NearAt Pl K L μ) :
    PairSp.embCLM.comp (concreteOps Pl K L μ).P =
      (jliftEOf Pl K L ((nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos) (SNop Pl K L μ)).comp
        ((Rop Pl L μ).comp (FAOp K L μ)) := by
  rw [concreteOps_eq Pl K L μ h]
  show PairSp.embCLM.comp ((concreteBase Pl K L μ h).jlift.comp
    ((concreteBase Pl K L μ h).R.comp (concreteBase Pl K L μ h).FA)) = _
  rw [← ContinuousLinearMap.comp_assoc, embCLM_comp_jlift]
  rfl

/-- `𝒬 = -𝒥v_Q Tc` (source 5817-5818), read through the embedding of `𝓔_ν`. -/
theorem concreteOps_embQ (μ : ℝ) (h : NearAt Pl K L μ) :
    PairSp.embCLM.comp (concreteOps Pl K L μ).Q =
      -((jliftEOf Pl K L ((nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos) (SNop Pl K L μ)).comp
        ((vQOf Pl K L μ).comp PairSp.TcL)) := by
  rw [concreteOps_eq Pl K L μ h]
  show PairSp.embCLM.comp (-((concreteBase Pl K L μ h).jlift.comp
    ((concreteBase Pl K L μ h).vQL.comp PairSp.TcL))) = _
  rw [ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc, embCLM_comp_jlift]
  rfl

/-- `L = 𝓛 Tc` (source 5815). -/
theorem concreteOps_Lg (μ : ℝ) (h : NearAt Pl K L μ) :
    (concreteOps Pl K L μ).Lg = (LjOp Pl K L μ).comp PairSp.TcL := by
  rw [concreteOps_eq Pl K L μ h]
  rfl

/-- `a_μ` of the return operators is the pinned `a_μ`. -/
theorem concreteOps_aMu (μ : ℝ) (h : NearAt Pl K L μ) : (concreteOps Pl K L μ).aMu = aMuOp K μ := by
  rw [concreteOps_eq Pl K L μ h]
  rfl

/-- `Λ_{μ,ν}` of the return operators is the pinned `Λ_{μ,ν}`. -/
theorem concreteOps_Lam (μ : ℝ) (h : NearAt Pl K L μ) :
    (concreteOps Pl K L μ).Lam = LamOp Pl K L μ := by
  rw [concreteOps_eq Pl K L μ h]
  rfl

end Formulas

/-! ## 3. Continuity of the products (source 5701-5704) -/

section Products

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
variable {X : Type} [TopologicalSpace X] {s : Set X}

/-- `x ↦ (f x, g x)` is norm continuous with `f` and `g`. -/
theorem continuousOn_clm_prod {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : X → E →L[ℝ] F} {g : X → E →L[ℝ] G} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).prod (g x)) s :=
  (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn (hf.prodMk hg)

/-- `x ↦ A ∘ F x` is norm continuous with `F`. -/
theorem continuousOn_comp_left {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F →L[ℝ] G) {f : X → E →L[ℝ] F} (h : ContinuousOn f s) :
    ContinuousOn (fun x => A ∘L f x) s :=
  (continuousOn_const (c := A)).clm_comp h

theorem jliftEOf_continuousOn {Dinv : X → LStr Pl K L →L[ℝ] LStr Pl K L}
    {SN : X → LStr Pl K L →L[ℝ] LVel Pl L} (hD : ContinuousOn Dinv s) (hS : ContinuousOn SN s) :
    ContinuousOn (fun x => jliftEOf Pl K L (Dinv x) (SN x)) s := by
  have h1 : ContinuousOn (fun x => (Dinv x).comp (multOp Pl K L)) s :=
    hD.clm_comp (continuousOn_const (c := multOp Pl K L))
  have h2a : ContinuousOn (fun x => ContinuousLinearMap.id ℝ (LVel Pl L) -
      (SN x).comp ((Dinv x).comp (multOp Pl K L))) s :=
    ContinuousOn.fun_sub (continuousOn_const (c := ContinuousLinearMap.id ℝ (LVel Pl L)))
      (hS.clm_comp h1)
  have h2 : ContinuousOn (fun x => Real.exp (-(gRate Pl / 8) / L.ν) •
      (ContinuousLinearMap.id ℝ (LVel Pl L) - (SN x).comp ((Dinv x).comp (multOp Pl K L)))) s :=
    h2a.fun_const_smul _
  have h3 := continuousOn_clm_prod h1 h2
  unfold jliftEOf
  exact continuousOn_comp_left _ h3

/-- `x ↦ A ∘ F x ∘ B` is norm continuous with `F` (fixed transports). -/
theorem continuousOn_sandwich {E₁ E₂ E₃ E₄ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] (A : E₃ →L[ℝ] E₄) (B : E₁ →L[ℝ] E₂)
    {F : X → E₂ →L[ℝ] E₃} (h : ContinuousOn F s) :
    ContinuousOn (fun x => A ∘L F x ∘L B) s :=
  (continuousOn_const (c := A)).clm_comp (h.clm_comp (continuousOn_const (c := B)))

/-- `S_N` on the return spaces is continuous with the near operator `S_N : Z → H`. -/
theorem SNop_continuousOn (μf : X → ℝ)
    (h : ContinuousOn (fun x => (nearOpsAt Pl K L (μf x)).SN) s) :
    ContinuousOn (fun x => SNop Pl K L (μf x)) s := by
  unfold SNop NearInst.NearOps.SNG NearInst.gainConjS
  refine ContinuousOn.fun_const_smul ?_ _
  refine continuousOn_sandwich _ _ ?_
  exact continuousOn_sandwich _ _ h

/-- **The polynomial near inverse** (source 3914-3917, 5703): where `D_N = I + M_US_N` is a unit
with `M_U = nearMU` (`NearAt`), `D_N⁻¹` on the return spaces is continuous with `S_N : Z → H`. -/
theorem DNinvG_continuousOn (μf : X → ℝ) (hnear : ∀ x ∈ s, NearAt Pl K L (μf x))
    (h : ContinuousOn (fun x => (nearOpsAt Pl K L (μf x)).SN) s) :
    ContinuousOn (fun x => (nearOpsAt Pl K L (μf x)).DNinvG (gRate Pl) L.ν_pos) s := by
  have hDN : ContinuousOn (fun x => (nearOpsAt Pl K L (μf x)).DN) s := by
    have h0 : ContinuousOn (fun x =>
        (1 : Zsp (cOf L.ν) K.mZ (L.ρb Pl K) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K)) +
          (nearMU Pl K L).comp (nearOpsAt Pl K L (μf x)).SN) s :=
      continuousOn_const.add (continuousOn_const.clm_comp h)
    refine h0.congr fun x hx => ?_
    show 1 + (nearOpsAt Pl K L (μf x)).MU.comp (nearOpsAt Pl K L (μf x)).SN = _
    rw [(hnear x hx).2]
  have hinv : ContinuousOn (fun x => Ring.inverse (nearOpsAt Pl K L (μf x)).DN) s := by
    intro x hx
    obtain ⟨u, hu⟩ := (hnear x hx).1
    have hc : ContinuousAt Ring.inverse (nearOpsAt Pl K L (μf x)).DN := by
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp_continuousWithinAt (f := fun y => (nearOpsAt Pl K L (μf y)).DN) hc
      (hDN x hx)
  unfold NearInst.NearOps.DNinvG NearInst.strConj conjG
  refine continuousOn_sandwich _ _ ?_
  exact continuousOn_sandwich _ _ hinv

theorem vQOf_continuousOn (μf : X → ℝ) (hS : ContinuousOn (fun x => Sop Pl K L (μf x)) s)
    (hSN : ContinuousOn (fun x => SNop Pl K L (μf x)) s)
    (hY : ContinuousOn (fun x => (wardOps Pl K L (μf x)).1) s)
    (hR : ContinuousOn (fun x => Rop Pl L (μf x)) s)
    (hE : ContinuousOn (fun x => (wardOps Pl K L (μf x)).2.2) s)
    (hEA : ContinuousOn (fun x => EAOp K L (μf x)) s)
    (hLj : ContinuousOn (fun x => LjOp Pl K L (μf x)) s)
    (hrA : ContinuousOn (fun x => rAOp Pl K L (μf x)) s) :
    ContinuousOn (fun x => vQOf Pl K L (μf x)) s :=
  ((hS.sub hSN).add hY).add (hR.clm_comp ((hE.sub (hEA.clm_comp hLj)).sub (hrA.clm_comp hLj)))

/-- **`𝒫` is norm continuous** where the near layer is invertible. -/
theorem concreteOps_P_continuousOn (μf : X → ℝ) (hnear : ∀ x ∈ s, NearAt Pl K L (μf x))
    (hD : ContinuousOn (fun x => (nearOpsAt Pl K L (μf x)).DNinvG (gRate Pl) L.ν_pos) s)
    (hSN : ContinuousOn (fun x => SNop Pl K L (μf x)) s)
    (hR : ContinuousOn (fun x => Rop Pl L (μf x)) s)
    (hF : ContinuousOn (fun x => FAOp K L (μf x)) s) :
    ContinuousOn (fun x => (concreteOps Pl K L (μf x)).P) s := by
  rw [PairSp.continuousOn_iff_embCLM]
  refine ((jliftEOf_continuousOn Pl K L hD hSN).clm_comp (hR.clm_comp hF)).congr ?_
  intro x hx
  exact concreteOps_embP Pl K L (μf x) (hnear x hx)

/-- **`𝒬` is norm continuous** where the near layer is invertible. -/
theorem concreteOps_Q_continuousOn (μf : X → ℝ) (hnear : ∀ x ∈ s, NearAt Pl K L (μf x))
    (hD : ContinuousOn (fun x => (nearOpsAt Pl K L (μf x)).DNinvG (gRate Pl) L.ν_pos) s)
    (hSN : ContinuousOn (fun x => SNop Pl K L (μf x)) s)
    (hvQ : ContinuousOn (fun x => vQOf Pl K L (μf x)) s) :
    ContinuousOn (fun x => (concreteOps Pl K L (μf x)).Q) s := by
  rw [PairSp.continuousOn_iff_embCLM]
  have hTc : ContinuousOn (fun _ : X => (PairSp.TcL : LGam Pl K L →L[ℝ] LStr Pl K L)) s :=
    continuousOn_const
  refine (((jliftEOf_continuousOn Pl K L hD hSN).clm_comp
    (hvQ.clm_comp hTc)).neg).congr ?_
  intro x hx
  exact concreteOps_embQ Pl K L (μf x) (hnear x hx)

/-- **`L` is norm continuous** where the near layer is invertible. -/
theorem concreteOps_Lg_continuousOn (μf : X → ℝ) (hnear : ∀ x ∈ s, NearAt Pl K L (μf x))
    (hLj : ContinuousOn (fun x => LjOp Pl K L (μf x)) s) :
    ContinuousOn (fun x => (concreteOps Pl K L (μf x)).Lg) s :=
  (hLj.clm_comp continuousOn_const).congr fun x hx => concreteOps_Lg Pl K L (μf x) (hnear x hx)

theorem concreteOps_aMu_continuousOn (μf : X → ℝ) (hnear : ∀ x ∈ s, NearAt Pl K L (μf x))
    (ha : ContinuousOn (fun x => aMuOp K (μf x)) s) :
    ContinuousOn (fun x => (concreteOps Pl K L (μf x)).aMu) s :=
  ha.congr fun x hx => concreteOps_aMu Pl K L (μf x) (hnear x hx)

theorem concreteOps_Lam_continuousOn (μf : X → ℝ) (hnear : ∀ x ∈ s, NearAt Pl K L (μf x))
    (hl : ContinuousOn (fun x => LamOp Pl K L (μf x)) s) :
    ContinuousOn (fun x => (concreteOps Pl K L (μf x)).Lam) s :=
  hl.congr fun x hx => concreteOps_Lam Pl K L (μf x) (hnear x hx)

end Products

/-! ## 4. The concrete sequence -/

/-- **Norm continuity at one level** (source 5684-5685, 5701-5704, 5918-5920): if the near layer is
invertible on `[-1,1]` and the primary operators are norm continuous on the window `μ_n([-1,1])`,
then `z ↦ 𝒫, L, 𝒬, a_μ, Λ_{μ,ν}` at `μ = μ_n(z)` are norm continuous on `[-1,1]`. -/
theorem normContinuousAt_of (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) (n : ℕ)
    (hnear : ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z))
    (hS : ContinuousOn (fun μ => Sop D.Pl D.K (D.level n) μ) (D.win n))
    (hR : ContinuousOn (fun μ => Rop D.Pl (D.level n) μ) (D.win n))
    (hY : ContinuousOn (fun μ => (wardOps D.Pl D.K (D.level n) μ).1) (D.win n))
    (hE : ContinuousOn (fun μ => (wardOps D.Pl D.K (D.level n) μ).2.2) (D.win n))
    (hN : ContinuousOn (fun μ => (nearOpsAt D.Pl D.K (D.level n) μ).SN) (D.win n))
    (hLj : ContinuousOn (fun μ => LjOp D.Pl D.K (D.level n) μ) (D.win n))
    (hF : ContinuousOn (fun μ => FAOp D.K (D.level n) μ) (D.win n))
    (hEA : ContinuousOn (fun μ => EAOp D.K (D.level n) μ) (D.win n))
    (hrA : ContinuousOn (fun μ => rAOp D.Pl D.K (D.level n) μ) (D.win n))
    (ha : ContinuousOn (fun μ => aMuOp D.K μ) (D.win n))
    (hL : ContinuousOn (fun μ => LamOp D.Pl D.K (D.level n) μ) (D.win n)) :
    (concreteReturnSeq D G).NormContinuousAt n := by
  have cN := D.continuousOn_comp_mu hN
  have cSN := SNop_continuousOn D.Pl D.K (D.level n) (D.mu n) cN
  have cD := DNinvG_continuousOn D.Pl D.K (D.level n) (D.mu n) hnear cN
  have cR := D.continuousOn_comp_mu hR
  have cLj := D.continuousOn_comp_mu hLj
  have cvQ := vQOf_continuousOn D.Pl D.K (D.level n) (D.mu n) (D.continuousOn_comp_mu hS) cSN
    (D.continuousOn_comp_mu hY) cR (D.continuousOn_comp_mu hE) (D.continuousOn_comp_mu hEA) cLj
    (D.continuousOn_comp_mu hrA)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact concreteOps_P_continuousOn D.Pl D.K (D.level n) (D.mu n) hnear cD cSN cR
      (D.continuousOn_comp_mu hF)
  · exact concreteOps_Lg_continuousOn D.Pl D.K (D.level n) (D.mu n) hnear cLj
  · exact concreteOps_Q_continuousOn D.Pl D.K (D.level n) (D.mu n) hnear cD cSN cvQ
  · exact concreteOps_aMu_continuousOn D.Pl D.K (D.level n) (D.mu n) hnear
      (D.continuousOn_comp_mu ha)
  · exact concreteOps_Lam_continuousOn D.Pl D.K (D.level n) (D.mu n) hnear
      (D.continuousOn_comp_mu hL)

/-- **`ConcreteReturnNormContinuity` from the leaves** (source 5684-5685, 5701-5704, 5918-5920):
the near layer is invertible on the window for large `n` (source 3943-3951, 5862-5866) and the
primary operators are norm continuous in `μ` on `μ_n([-1,1])` (`Continuity/Defs.lean`). -/
theorem returnNormContinuity_concrete_of (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)))
    (hnear : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z))
    (hS : D.SopCont) (hR : D.RopCont) (hY : D.WardYCont) (hE : D.WardECont) (hN : D.NearSNCont)
    (hLj : D.LjCont) (hF : D.FACont) (hEA : D.EACont) (hrA : D.RACont) (ha : D.AMuCont)
    (hL : D.LamCont) : ConcreteReturnNormContinuity D G := by
  filter_upwards [hnear, hS, hR, hY, hE, hN, hLj, hF, hEA, hrA, ha, hL] with n h0 h1 h2 h3 h4 h5
    h6 h7 h8 h9 h10 h11
  exact normContinuousAt_of D G n h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

/-- **`ConcreteReturnNormContinuity` under the standing hypotheses** of the repair section
(`SeqData.RepairStanding`, whose field `near` is the invertibility of the near layer on the window),
from the leaves `SopCont`, `RopCont`, `WardYCont`, `WardECont`, `NearSNCont`, `LjCont`, `FACont`,
`EACont`, `RACont`, `LamCont` (`AMuCont` is `SeqData.aMuCont`). -/
theorem returnNormContinuity_concrete_of_standing (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)))
    (hS : D.SopCont) (hR : D.RopCont) (hY : D.WardYCont) (hE : D.WardECont) (hN : D.NearSNCont)
    (hLj : D.LjCont) (hF : D.FACont) (hEA : D.EACont) (hrA : D.RACont) (hL : D.LamCont) :
    ConcreteReturnNormContinuity D G :=
  returnNormContinuity_concrete_of D G hst.near hS hR hY hE hN hLj hF hEA hrA (D.aMuCont hst) hL

end UnforcedLeray.Short.PartIIIb.Concrete
