import UnforcedLeray.Short.PartI.Sub.PartI_T08_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth.Schwartz

/-!
# Part I, task `PartI:T08/1/2` (`qcSmooth_proof`): smoothness of `Q_c`

Source: `the November 2 reference manuscript`, lines 326-329. The Prop is `QcSmooth`
in `Sub/PartI_T08_1.lean`.

Reduction (proved here): `Qc = B0146.crossStress` (`Train.Qc_eq`), and by `B0146.crossStress_eq`
`Q_c^{kl} = L[u_k] L[u_l] - L[u_k u_l]`, where `L[g] = B0146.latticeSum c g` equals the
periodization `Gaussian.periodize c g` (definitionally). `Gaussian.contDiff_periodize` (with
`s = 2`) makes each lattice sum `C^∞` once `g` is `C^∞` with all derivatives `O((1+|q|)^{-2})`.

The leaf `LatticeProfileLeaf` (smoothness and decay of the isolated heat-velocity components
`uc k a` and their products) is proved: they are Gaussian times polynomial, hence Schwartz
(`QcSmooth/Schwartz.lean`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- A profile `g` whose periodization is `C^∞` by `Gaussian.contDiff_periodize`: smooth, with every
derivative `O((1+|q|)^{-2})` uniformly in the `η`-variable. -/
def LatticeProfileDecay (g : Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ z : Plane,
    ‖iteratedFDeriv ℝ n g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))

/-- **Leaf** (proved below): for every width `a > 0` and components `k l`, the isolated velocity component
`uc k a` and the product `uc k a * uc l a` satisfy `LatticeProfileDecay`. -/
def LatticeProfileLeaf : Prop :=
  ∀ a : ℝ, 0 < a → ∀ k l : Fin 2,
    LatticeProfileDecay (UnforcedLeray.B0146.uc k a) ∧
      LatticeProfileDecay (fun x => UnforcedLeray.B0146.uc k a x * UnforcedLeray.B0146.uc l a x)

theorem SchFn_uc {a : ℝ} (ha : 0 < a) (k : Fin 2) :
    QcSmoothAux.SchFn (UnforcedLeray.B0146.uc k a) := by
  have hg := QcSmoothAux.SchFn.gauss (b := a⁻¹ / 4) (by positivity)
  have e : ∀ z : Plane, UnforcedLeray.B0113.gw a z =
      Real.exp (-(a⁻¹ / 4 * (z.1 ^ 2 + z.2 ^ 2))) := fun z => by
    unfold UnforcedLeray.B0113.gw UnforcedLeray.GaussianVortex.radiusSq
    congr 1; ring
  fin_cases k
  · obtain ⟨s, hs⟩ := (hg.mul_snd.const_mul (-(a⁻¹ ^ 2)))
    refine ⟨s, ?_⟩
    rw [hs]; funext z
    simp [UnforcedLeray.B0146.uc, UnforcedLeray.B0146.vcomp, UnforcedLeray.B0113.vExp, e]
    ring
  · obtain ⟨s, hs⟩ := (hg.mul_fst.const_mul (a⁻¹ ^ 2))
    refine ⟨s, ?_⟩
    rw [hs]; funext z
    simp [UnforcedLeray.B0146.uc, UnforcedLeray.B0146.vcomp, UnforcedLeray.B0113.vExp, e]
    ring

theorem LatticeProfileDecay_of_SchFn {g : Plane → ℝ} (h : QcSmoothAux.SchFn g) :
    LatticeProfileDecay g := ⟨h.contDiff, h.decay⟩

/-- The leaf: Gaussian-times-polynomial profiles are Schwartz. -/
theorem latticeProfileLeaf_proof : LatticeProfileLeaf := by
  intro a ha k l
  exact ⟨LatticeProfileDecay_of_SchFn (SchFn_uc ha k),
    LatticeProfileDecay_of_SchFn ((SchFn_uc ha k).mul (SchFn_uc ha l))⟩

/-- `QcSmooth` from the leaf `LatticeProfileLeaf`. -/
theorem qcSmooth_of_leaf (hL : LatticeProfileLeaf) : UnforcedLeray.Short.PartI.QcSmooth := by
  intro ν c s hν hc hs k l
  have hc0 : c ≠ 0 := hc.ne'
  have ha : 0 < UnforcedLeray.B0113.heatWidth ν s := UnforcedLeray.B0113.heatWidth_pos hν hs
  have hsm : ∀ g : Plane → ℝ, LatticeProfileDecay g →
      ContDiff ℝ ∞ (fun z => UnforcedLeray.B0146.latticeSum c g z) := by
    intro g hg
    exact UnforcedLeray.Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc0 hg.1
      (fun n _ => hg.2 n)
  have hfun : (fun z => UnforcedLeray.Train.Qc ν c s z k l) = fun z =>
      UnforcedLeray.B0146.latticeSum c (UnforcedLeray.B0146.uc k (UnforcedLeray.B0113.heatWidth ν s)) z *
        UnforcedLeray.B0146.latticeSum c (UnforcedLeray.B0146.uc l (UnforcedLeray.B0113.heatWidth ν s)) z -
      UnforcedLeray.B0146.latticeSum c
        (fun x => UnforcedLeray.B0146.uc k (UnforcedLeray.B0113.heatWidth ν s) x *
          UnforcedLeray.B0146.uc l (UnforcedLeray.B0113.heatWidth ν s) x) z := by
    funext z
    rw [UnforcedLeray.Train.Qc_eq, UnforcedLeray.B0146.crossStress_eq hc0 ha z k l]
  rw [hfun]
  have h := hL _ ha k l
  exact ((hsm _ h.1).mul (hsm _ (hL _ ha l l).1)).sub (hsm _ h.2)

/-- **Target.** -/
theorem qcSmooth_proof : UnforcedLeray.Short.PartI.QcSmooth :=
  qcSmooth_of_leaf latticeProfileLeaf_proof

end UnforcedLeray.Short.PartI
