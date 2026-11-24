import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# Part I, task `PartI:T02/3` (helper): reflection identities for the momentum residual and divergence

Source of record: `the November 2 reference manuscript`, line 288 ("Uniqueness gives
`v(-q,-eta,s) = -v(q,eta,s)`").  The reflected pair `(reflV v, reflP p) = (-v(s,-z), p(s,-z))`
solves the same equations: the momentum residual of the reflected pair at `z` is minus the residual
of `(v,p)` at `-z`, and the divergence of the reflected velocity at `z` is the divergence at `-z`.

Both identities are unconditional: every operator is defined by `deriv` of a slice (`Train.advection`,
`Train.vecLaplacian`, `Train.gradS`, `Cyl.partialQ`, `Cyl.partialEta`), and `deriv` commutes with the
sign change of the variable (`deriv_comp_neg`).  All helper names carry the prefix `ro`.
-/

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open Set Filter MeasureTheory
open scoped ContDiff Topology

/-! ### Partial derivatives and the sign change -/

theorem ro_partialQ_neg_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) (z : Plane) :
    Cyl.partialQ (fun w => -f w) z = -Cyl.partialQ f z := by
  show deriv (fun q : ℝ => -f (q, z.2)) z.1 = -deriv (fun q : ℝ => f (q, z.2)) z.1
  exact deriv.neg

theorem ro_partialEta_neg_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) (z : Plane) :
    Cyl.partialEta (fun w => -f w) z = -Cyl.partialEta f z := by
  show deriv (fun η : ℝ => -f (z.1, η)) z.2 = -deriv (fun η : ℝ => f (z.1, η)) z.2
  exact deriv.neg

theorem ro_partialQ_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) (z : Plane) :
    Cyl.partialQ (fun w => f (-w)) z = -Cyl.partialQ f (-z) := by
  show deriv (fun q : ℝ => f (-(q, z.2))) z.1 = -deriv (fun q : ℝ => f (q, -z.2)) (-z.1)
  have h1 : (fun q : ℝ => f (-(q, z.2))) = fun q : ℝ => (fun q' : ℝ => f (q', -z.2)) (-q) := by
    funext q
    simp
  rw [h1]
  exact deriv_comp_neg (fun q' : ℝ => f (q', -z.2)) z.1

theorem ro_partialEta_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) (z : Plane) :
    Cyl.partialEta (fun w => f (-w)) z = -Cyl.partialEta f (-z) := by
  show deriv (fun η : ℝ => f (-(z.1, η))) z.2 = -deriv (fun η : ℝ => f (-z.1, η)) (-z.2)
  have h1 : (fun η : ℝ => f (-(z.1, η))) = fun η : ℝ => (fun η' : ℝ => f (-z.1, η')) (-η) := by
    funext η
    simp
  rw [h1]
  exact deriv_comp_neg (fun η' : ℝ => f (-z.1, η')) z.2

/-- Reflection of a scalar function, with the sign of the reflected field: `∂_q` of `-f(-·)`. -/
theorem ro_partialQ_refl (f : Plane → ℝ) (z : Plane) :
    Cyl.partialQ (fun w => -f (-w)) z = Cyl.partialQ f (-z) := by
  rw [ro_partialQ_neg_fun, ro_partialQ_comp_neg, neg_neg]

theorem ro_partialEta_refl (f : Plane → ℝ) (z : Plane) :
    Cyl.partialEta (fun w => -f (-w)) z = Cyl.partialEta f (-z) := by
  rw [ro_partialEta_neg_fun, ro_partialEta_comp_neg, neg_neg]

/-! ### Laplacian under the sign change -/

theorem ro_partialQ_partialQ_comp_neg (f : Plane → ℝ) (z : Plane) :
    Cyl.partialQ (Cyl.partialQ (fun w => f (-w))) z = Cyl.partialQ (Cyl.partialQ f) (-z) := by
  have h : Cyl.partialQ (fun w => f (-w)) = fun w => -Cyl.partialQ f (-w) :=
    funext fun w => ro_partialQ_comp_neg f w
  rw [h, ro_partialQ_neg_fun, ro_partialQ_comp_neg, neg_neg]

theorem ro_partialEta_partialEta_comp_neg (f : Plane → ℝ) (z : Plane) :
    Cyl.partialEta (Cyl.partialEta (fun w => f (-w))) z
      = Cyl.partialEta (Cyl.partialEta f) (-z) := by
  have h : Cyl.partialEta (fun w => f (-w)) = fun w => -Cyl.partialEta f (-w) :=
    funext fun w => ro_partialEta_comp_neg f w
  rw [h, ro_partialEta_neg_fun, ro_partialEta_comp_neg, neg_neg]

theorem ro_lapS_comp_neg (f : Plane → ℝ) (z : Plane) :
    Train.lapS (fun w => f (-w)) z = Train.lapS f (-z) := by
  unfold Train.lapS
  rw [ro_partialQ_partialQ_comp_neg, ro_partialEta_partialEta_comp_neg]

theorem ro_lapS_neg_fun (f : Plane → ℝ) (z : Plane) :
    Train.lapS (fun w => -f w) z = -Train.lapS f z := by
  have hQ : Cyl.partialQ (fun w => -f w) = fun w => -Cyl.partialQ f w :=
    funext fun w => ro_partialQ_neg_fun f w
  have hE : Cyl.partialEta (fun w => -f w) = fun w => -Cyl.partialEta f w :=
    funext fun w => ro_partialEta_neg_fun f w
  unfold Train.lapS
  rw [hQ, hE, ro_partialQ_neg_fun, ro_partialEta_neg_fun]
  ring

theorem ro_lapS_refl (f : Plane → ℝ) (z : Plane) :
    Train.lapS (fun w => -f (-w)) z = -Train.lapS f (-z) := by
  have h := ro_lapS_neg_fun (fun w => f (-w)) z
  rw [ro_lapS_comp_neg f z] at h
  exact h

/-! ### Vector operators under the sign change (`z ↦ -z`, field `w ↦ -v(-w)`) -/

theorem ro_advection_refl (v : Plane → Vec) (z : Plane) :
    Train.advection (fun w => -v (-w)) z = -Train.advection v (-z) := by
  have h00 : Cyl.partialQ (fun w => -(v (-w) 0)) z = Cyl.partialQ (fun w => v w 0) (-z) :=
    ro_partialQ_refl (fun w => v w 0) z
  have h01 : Cyl.partialEta (fun w => -(v (-w) 0)) z = Cyl.partialEta (fun w => v w 0) (-z) :=
    ro_partialEta_refl (fun w => v w 0) z
  have h10 : Cyl.partialQ (fun w => -(v (-w) 1)) z = Cyl.partialQ (fun w => v w 1) (-z) :=
    ro_partialQ_refl (fun w => v w 1) z
  have h11 : Cyl.partialEta (fun w => -(v (-w) 1)) z = Cyl.partialEta (fun w => v w 1) (-z) :=
    ro_partialEta_refl (fun w => v w 1) z
  apply Train.Vec.ext
  · simp only [Train.advection, Train.toVec_zero, PiLp.neg_apply, h00, h01]
    ring
  · simp only [Train.advection, Train.toVec_one, PiLp.neg_apply, h10, h11]
    ring

theorem ro_vecLaplacian_refl (v : Plane → Vec) (z : Plane) :
    Train.vecLaplacian (fun w => -v (-w)) z = -Train.vecLaplacian v (-z) := by
  have h0 : Train.lapS (fun w => -(v (-w) 0)) z = -Train.lapS (fun w => v w 0) (-z) :=
    ro_lapS_refl (fun w => v w 0) z
  have h1 : Train.lapS (fun w => -(v (-w) 1)) z = -Train.lapS (fun w => v w 1) (-z) :=
    ro_lapS_refl (fun w => v w 1) z
  apply Train.Vec.ext
  · simp only [Train.vecLaplacian, Train.toVec_zero, PiLp.neg_apply, h0]
  · simp only [Train.vecLaplacian, Train.toVec_one, PiLp.neg_apply, h1]

theorem ro_gradS_refl (p : Plane → ℝ) (z : Plane) :
    Train.gradS (fun w => p (-w)) z = -Train.gradS p (-z) := by
  apply Train.Vec.ext
  · simp only [Train.gradS, Train.toVec_zero, PiLp.neg_apply]
    exact ro_partialQ_comp_neg p z
  · simp only [Train.gradS, Train.toVec_one, PiLp.neg_apply]
    exact ro_partialEta_comp_neg p z

theorem ro_divergence_refl (v : Plane → Vec) (z : Plane) :
    Cyl.divergence (fun w => -v (-w)) z = Cyl.divergence v (-z) := by
  have h0 : Cyl.partialQ (fun w => -(v (-w) 0)) z = Cyl.partialQ (fun w => v w 0) (-z) :=
    ro_partialQ_refl (fun w => v w 0) z
  have h1 : Cyl.partialEta (fun w => -(v (-w) 1)) z = Cyl.partialEta (fun w => v w 1) (-z) :=
    ro_partialEta_refl (fun w => v w 1) z
  unfold Cyl.divergence
  simp only [PiLp.neg_apply, h0, h1]

/-- Time derivative of the reflected velocity: `∂_s (-v(s,-z)) = -∂_s v(s,-z)`. -/
theorem ro_deriv_refl (v : ℝ → Plane → Vec) (s : ℝ) (z : Plane) :
    deriv (fun t => reflV v t z) s = -deriv (fun t => v t (-z)) s := by
  show deriv (fun t => -v t (-z)) s = -deriv (fun t => v t (-z)) s
  exact deriv.neg

/-! ### The reflected pair solves the same equations -/

/-- The momentum residual of the reflected pair at `z` is minus the residual at `-z`, and the
divergence of the reflected velocity at `z` is the divergence at `-z` (no regularity needed). -/
theorem reflect_residual_identities (ν : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (s : ℝ)
    (z : Plane) :
    Train.momentumResidual ν (reflV v) (reflP p) s z = -Train.momentumResidual ν v p s (-z) ∧
      Cyl.divergence (reflV v s) z = Cyl.divergence (v s) (-z) := by
  refine ⟨?_, ?_⟩
  · have ht : deriv (fun t => reflV v t z) s = -deriv (fun t => v t (-z)) s :=
      ro_deriv_refl v s z
    have ha : Train.advection (reflV v s) z = -Train.advection (v s) (-z) :=
      ro_advection_refl (v s) z
    have hv : Train.vecLaplacian (reflV v s) z = -Train.vecLaplacian (v s) (-z) :=
      ro_vecLaplacian_refl (v s) z
    have hp : Train.gradS (reflP p s) z = -Train.gradS (p s) (-z) :=
      ro_gradS_refl (p s) z
    unfold Train.momentumResidual
    rw [ht, ha, hv, hp, smul_neg]
    abel
  · exact ro_divergence_refl (v s) z

end UnforcedLeray.Short.PartI
