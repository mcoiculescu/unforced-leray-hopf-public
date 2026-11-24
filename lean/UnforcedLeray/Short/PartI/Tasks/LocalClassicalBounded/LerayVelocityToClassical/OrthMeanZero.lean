import UnforcedLeray.Short.PartI.Sub.T02_1_5

/-!
# Part I, task `PartI:T02/1/5/3`: horizontal mean zero of an orthogonal field

Source of record: `the November 2 reference manuscript`, lines 261-288.
Target: `orthMeanZero : OrthMeanZero` (definition in `Short/PartI/Sub/T02_1_5.lean`).

Proof.  Test the orthogonality hypothesis with the solenoidal fields `(ψ(η), 0)`, where `ψ` is
smooth with compact support.  Fubini on the cell gives `∫ ψ(η) m(η) dη = 0` for
`m(η) = ∫_{-c/2}^{c/2} g₁(q,η) dq`.  The function `m` is continuous, so the fundamental lemma
gives `m = 0` everywhere.  Periodicity of `g₁(·,η)` moves `[-c/2, c/2]` to `[0, c]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec toVecL)
open UnforcedLeray.Cyl (Plane)

theorem orthMeanZero : OrthMeanZero := by
  unfold OrthMeanZero
  intro c g hc hg hper hortho η
  have hgc : Continuous g := hg.continuous
  have hg0 : Continuous fun z : Plane => g z 0 := by fun_prop
  have hle : -c / 2 ≤ c / 2 := by linarith
  -- the horizontal mean `m(η) = ∫_{-c/2}^{c/2} g₁(q,η) dq`
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ η' : ℝ, m η' = ∫ q in (-c / 2)..(c / 2), g (q, η') 0 :=
    ⟨fun η' => ∫ q in (-c / 2)..(c / 2), g (q, η') 0, fun _ => rfl⟩
  have hmeq : m = fun η' => ∫ q in (-c / 2)..(c / 2), g (q, η') 0 := funext hm
  have hm_cont : Continuous m := by
    rw [hmeq]
    have hunc : Continuous (Function.uncurry fun (η' : ℝ) (q : ℝ) => g (q, η') 0) :=
      hg0.comp (continuous_snd.prodMk continuous_fst)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hunc _ _
  have hm_locint : LocallyIntegrable m volume := hm_cont.locallyIntegrable
  have hm_Ico : ∀ η' : ℝ, ∫ q in Ico (-c / 2) (c / 2), g (q, η') 0 = m η' := by
    intro η'
    rw [integral_Ico_eq_integral_Ioc, hm η', intervalIntegral.integral_of_le hle]
  -- the orthogonality hypothesis against the tests `(ψ(η), 0)`
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ η', m η' * ψ η' = 0 := by
    intro ψ hψ hψc
    have hT : ContDiff ℝ ∞ (fun v : ℝ × ℝ => toVec v) := toVecL.contDiff
    have hφs : ContDiff ℝ ∞ (fun z : Plane => toVec (ψ z.2, 0)) :=
      hT.comp ((hψ.comp contDiff_snd).prodMk contDiff_const)
    have hφp : Cyl.IsPeriodic c (fun z : Plane => toVec (ψ z.2, 0)) := fun _ => rfl
    have hφd : ∀ z : Plane, Cyl.divergence (fun z : Plane => toVec (ψ z.2, 0)) z = 0 := by
      intro z
      simp [Cyl.divergence, Cyl.partialQ, Cyl.partialEta]
    obtain ⟨R, hR⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hψc.isCompact.isBounded
    have hφsup : ∃ R : ℝ, ∀ z : Plane, R < |z.2| → toVec (ψ z.2, 0) = 0 := by
      refine ⟨R, fun z hz => ?_⟩
      have hψz : ψ z.2 = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h := hR hmem
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
        linarith
      ext i
      fin_cases i <;> simp [hψz]
    have hpt : ∀ z : Plane, inner ℝ (g z) (toVec (ψ z.2, 0)) = g z 0 * ψ z.2 := by
      intro z
      simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
    have hcellint : IntegrableOn (fun z : Plane => g z 0 * ψ z.2) (Cyl.cell c) := by
      have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ tsupport ψ) :=
        isCompact_Icc.prod hψc.isCompact
      have hF : Continuous fun z : Plane => g z 0 * ψ z.2 :=
        hg0.mul (hψ.continuous.comp continuous_snd)
      refine IntegrableOn.of_forall_sdiff_eq_zero
        (hF.continuousOn.integrableOn_compact hK) (Cyl.measurableSet_cell c) ?_
      intro x hx
      obtain ⟨hxc, hxK⟩ := hx
      have h1 : x.1 ∈ Icc (-c / 2) (c / 2) := by
        rw [Cyl.mem_cell] at hxc
        exact ⟨hxc.1, le_of_lt hxc.2⟩
      have h2 : x.2 ∉ tsupport ψ := fun h => hxK (Set.mem_prod.mpr ⟨h1, h⟩)
      simp [image_eq_zero_of_notMem_tsupport h2]
    have hzero : ∫ z in Cyl.cell c, inner ℝ (g z) (toVec (ψ z.2, 0)) = 0 :=
      hortho (fun z : Plane => toVec (ψ z.2, 0)) hφs hφp hφd hφsup
    simp only [hpt] at hzero
    rw [Cyl.integral_cell_eq_integral_integral hcellint] at hzero
    simp only [integral_mul_const, hm_Ico] at hzero
    exact hzero
  -- fundamental lemma, then continuity: `m = 0`
  have hmae : ∀ᵐ x ∂(volume : Measure ℝ), m x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hm_locint
    intro ψ hψ hψc
    have hfun : (fun x => ψ x • m x) = fun x => m x * ψ x :=
      funext fun x => by rw [smul_eq_mul, mul_comm]
    rw [hfun]
    exact key ψ hψ hψc
  have hcz : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hm0 : m = fun _ => (0 : ℝ) := (hm_cont.ae_eq_iff_eq volume hcz).mp hmae
  -- periodicity: `∫_0^c = ∫_{-c/2}^{c/2}`
  have hP : Function.Periodic (fun q : ℝ => g (q, η) 0) c := by
    intro x
    exact congrArg (fun v : Vec => v 0) (hper (x, η))
  have h1 := hP.intervalIntegral_add_eq (-c / 2) 0
  have h2 : -c / 2 + c = c / 2 := by ring
  rw [h2, zero_add] at h1
  calc ∫ q in (0 : ℝ)..c, g (q, η) 0 = ∫ q in (-c / 2)..(c / 2), g (q, η) 0 := h1.symm
    _ = m η := (hm η).symm
    _ = 0 := congrFun hm0 η

end UnforcedLeray.Short.PartI
