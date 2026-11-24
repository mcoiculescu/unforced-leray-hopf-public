import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.QSwap

/-!
# Part II-b, leaf `PartII-b:G4/3/6/2/3/4`: `PsiFirstJets`

Source of record: `the November 2 reference manuscript` 2419-2423 (jets of the
stream), 261-291 (`v = ∇^⊥ψ`).

For `s > 0`, the first jets of `ψ` are the derivatives of `F = ψ_s` (for `j = 1`, `ℓ = 0`) and of
`s ↦ ∂_s ψ` (for `ℓ = 1`). Their derivative at `z` is a linear map on the sup-norm plane whose
values on `(1,0)` and `(0,1)` are, by `PsiQSwap` and `PsiEtaSwap` (and the stream relation
`v = ∇^⊥ψ`), the components `v₁` and `-v₀` (resp. `∂_s v₁`, `-∂_s v₀`). A linear map on the sup
norm plane with these values has operator norm at most `|a| + |b| ≤ 2‖·‖` of the Euclidean norm
of `v`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Operator norm bound on the sup-norm plane: a linear form with `L(1,0) = w₁`, `L(0,1) = -w₀`
has norm at most `2‖w‖`. -/
private lemma psiFJ_opNorm_le {L : UnforcedLeray.Cyl.Plane →L[ℝ] ℝ}
    {w : UnforcedLeray.Train.Vec}
    (h1 : L (1, 0) = w 1) (h0 : L (0, 1) = -(w 0)) : ‖L‖ ≤ 2 * ‖w‖ := by
  have hw0 : ‖w 0‖ ≤ ‖w‖ := PiLp.norm_apply_le w 0
  have hw1 : ‖w 1‖ ≤ ‖w‖ := PiLp.norm_apply_le w 1
  refine L.opNorm_le_bound (by positivity) fun h => ?_
  have hdec : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hL : L h = h.1 * w 1 + h.2 * (-(w 0)) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, map_smul, h1, h0, smul_eq_mul, smul_eq_mul]
  have ha : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have hb : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have e1 : ‖h.1 * w 1‖ ≤ ‖h‖ * ‖w‖ := by
    rw [norm_mul]; exact mul_le_mul ha hw1 (norm_nonneg _) (norm_nonneg _)
  have e2 : ‖h.2 * (-(w 0))‖ ≤ ‖h‖ * ‖w‖ := by
    rw [norm_mul, norm_neg]; exact mul_le_mul hb hw0 (norm_nonneg _) (norm_nonneg _)
  rw [hL]
  have e3 := norm_add_le (h.1 * w 1) (h.2 * (-(w 0)))
  nlinarith [e1, e2, e3]

/-- Derivative along the first coordinate line of a differentiable function on the plane. -/
private lemma psiFJ_hasDerivAt_fst {G : UnforcedLeray.Cyl.Plane → ℝ} {z : UnforcedLeray.Cyl.Plane}
    (hG : DifferentiableAt ℝ G z) :
    HasDerivAt (fun x : ℝ => G (x, z.2)) (fderiv ℝ G z (1, 0)) z.1 :=
  hG.hasFDerivAt.comp_hasDerivAt z.1 ((hasDerivAt_id' z.1).prodMk (hasDerivAt_const z.1 z.2))

/-- Derivative along the second coordinate line of a differentiable function on the plane. -/
private lemma psiFJ_hasDerivAt_snd {G : UnforcedLeray.Cyl.Plane → ℝ} {z : UnforcedLeray.Cyl.Plane}
    (hG : DifferentiableAt ℝ G z) :
    HasDerivAt (fun y : ℝ => G (z.1, y)) (fderiv ℝ G z (0, 1)) z.2 :=
  hG.hasFDerivAt.comp_hasDerivAt z.2 ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id' z.2))

private lemma psiFJ_fst_eq {G : UnforcedLeray.Cyl.Plane → ℝ} {z : UnforcedLeray.Cyl.Plane}
    (hG : DifferentiableAt ℝ G z) {a : ℝ}
    (ha : HasDerivAt (fun x : ℝ => G (x, z.2)) a z.1) : fderiv ℝ G z (1, 0) = a :=
  (psiFJ_hasDerivAt_fst hG).unique ha

private lemma psiFJ_snd_eq {G : UnforcedLeray.Cyl.Plane → ℝ} {z : UnforcedLeray.Cyl.Plane}
    (hG : DifferentiableAt ℝ G z) {a : ℝ}
    (ha : HasDerivAt (fun y : ℝ => G (z.1, y)) a z.2) : fderiv ℝ G z (0, 1) = a :=
  (psiFJ_hasDerivAt_snd hG).unique ha

/-- `∂_q G = D G (1,0)` at a point of differentiability (the classical partial). -/
private lemma psiFJ_partialX_eq {G : UnforcedLeray.Cyl.Plane → ℝ} {z : UnforcedLeray.Cyl.Plane}
    (hG : DifferentiableAt ℝ G z) :
    UnforcedLeray.GaussianVortex.partialX G z = fderiv ℝ G z (1, 0) :=
  (psiFJ_hasDerivAt_fst hG).deriv

private lemma psiFJ_partialY_eq {G : UnforcedLeray.Cyl.Plane → ℝ} {z : UnforcedLeray.Cyl.Plane}
    (hG : DifferentiableAt ℝ G z) :
    UnforcedLeray.GaussianVortex.partialY G z = fderiv ℝ G z (0, 1) :=
  (psiFJ_hasDerivAt_snd hG).deriv

/-- Norm of a first jet of a scalar field in the spatial variable. -/
private lemma psiFJ_norm_ageJet_one (ℓ : ℕ) (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s : ℝ)
    (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet ℓ 1 F s z‖ =
      ‖fderiv ℝ (fun z' => iteratedDeriv ℓ (fun r => F r z') s) z‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, norm_iteratedFDeriv_one]

/-- Norm of a zeroth jet is the norm of the age derivative. -/
private lemma psiFJ_norm_ageJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℕ) (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 F s z‖ = ‖iteratedDeriv ℓ (fun r => F r z) s‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, norm_iteratedFDeriv_zero]

/-- The `ℓ = 0`, `j = 1` jet bound: `‖Dψ_s‖ ≤ 2‖v‖` (SP 2419-2423, 261-291). -/
private lemma psiFJ_first (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec)
    (hsp : IsStreamPair ψ v) (s : ℝ) (hs : 0 < s) (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 0 1 ψ s z‖ ≤
      2 * ‖UnforcedLeray.Short.PartI.ageJet 0 0 v s z‖ := by
  obtain ⟨hΨ, _, hst⟩ := hsp
  have hK : ContDiffAt ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => ψ x.1 x.2) (s, z) :=
    hΨ.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  have hf : ContDiffAt ℝ ∞ (fun z' : UnforcedLeray.Cyl.Plane => (s, z')) z :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  have hC : ContDiffAt ℝ ∞ (fun z' : UnforcedLeray.Cyl.Plane => ψ s z') z := hK.comp z hf
  have hD : DifferentiableAt ℝ (fun z' : UnforcedLeray.Cyl.Plane => ψ s z') z :=
    hC.differentiableAt (by simp)
  have hw := hst s hs z
  have hw1 : v s z 1 = UnforcedLeray.GaussianVortex.partialX (ψ s) z := by
    rw [hw]; simp [UnforcedLeray.GaussianVortex.perpendicularGradient,
      UnforcedLeray.Train.toVec_one]
  have hw0 : v s z 0 = -UnforcedLeray.GaussianVortex.partialY (ψ s) z := by
    rw [hw]; simp [UnforcedLeray.GaussianVortex.perpendicularGradient,
      UnforcedLeray.Train.toVec_zero]
  have h1 : fderiv ℝ (fun z' => ψ s z') z (1, 0) = v s z 1 := by
    rw [hw1]; exact (psiFJ_partialX_eq hD).symm
  have h0 : fderiv ℝ (fun z' => ψ s z') z (0, 1) = -(v s z 0) := by
    rw [hw0, neg_neg]; exact (psiFJ_partialY_eq hD).symm
  rw [psiFJ_norm_ageJet_one 0 ψ s z, psiFJ_norm_ageJet_zero 0 v s z]
  simp only [iteratedDeriv_zero]
  exact psiFJ_opNorm_le h1 h0

/-- The `ℓ = 1`, `j = 1` jet bound: `‖D∂_sψ‖ ≤ 2‖∂_s v‖` (SP 2419-2423, using `PsiQSwap`,
`PsiEtaSwap`). -/
private lemma psiFJ_second (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec)
    (hsp : IsStreamPair ψ v) (s : ℝ) (hs : 0 < s) (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 1 1 ψ s z‖ ≤
      2 * ‖UnforcedLeray.Short.PartI.ageJet 1 0 v s z‖ := by
  obtain ⟨hΨ, _, _⟩ := id hsp
  have hC := psiJet_slice_contDiffAt (fun x : ℝ × UnforcedLeray.Cyl.Plane => ψ x.1 x.2) hΨ 1 1
    hs z
  have hf : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun z' : UnforcedLeray.Cyl.Plane => (s, z')) z :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  have hG : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun z' : UnforcedLeray.Cyl.Plane => iteratedDeriv 1 (fun r => ψ r z') s) z :=
    hC.comp z hf
  have hDG : DifferentiableAt ℝ
      (fun z' : UnforcedLeray.Cyl.Plane => iteratedDeriv 1 (fun r => ψ r z') s) z :=
    hG.differentiableAt (by norm_num)
  have hL10 : fderiv ℝ (fun z' : UnforcedLeray.Cyl.Plane => iteratedDeriv 1 (fun r => ψ r z') s) z
      (1, 0) = iteratedDeriv 1 (fun r => v r z) s 1 :=
    psiFJ_fst_eq hDG (psiQSwap_proof ψ v hsp 1 s hs z.1 z.2)
  have hL01 : fderiv ℝ (fun z' : UnforcedLeray.Cyl.Plane => iteratedDeriv 1 (fun r => ψ r z') s) z
      (0, 1) = -(iteratedDeriv 1 (fun r => v r z) s 0) :=
    psiFJ_snd_eq hDG (psiEtaSwap_proof ψ v hsp 1 s hs z.1 z.2)
  rw [psiFJ_norm_ageJet_one 1 ψ s z, psiFJ_norm_ageJet_zero 1 v s z]
  exact psiFJ_opNorm_le hL10 hL01

end UnforcedLeray.Short.IIb

/-- **First jets of the stream** (SP 2419-2423), leaf `PartII-b:G4/3/6/2/3/4`. -/
theorem psiFirstJets_proof : UnforcedLeray.Short.IIb.PsiFirstJets := by
  intro ψ v hsp s hs z
  exact ⟨UnforcedLeray.Short.IIb.psiFJ_first ψ v hsp s hs z,
    UnforcedLeray.Short.IIb.psiFJ_second ψ v hsp s hs z⟩
