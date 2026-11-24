import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestComm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestSymm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneTestSub

/-!
# Leaf `PartII-b:T12/1/1/2/46`: the `L²` Riesz pairs are mutually transpose

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For tests, `∫ S_{ik} f · g = ∫ f · S_{ik} g` (`RieszTestSymm`) and `S_{ik} g = S_{ki} g`
(`RieszTestComm`).  Both sides of the identity for the `L²` extensions are continuous bilinear
in `(f, g)`, so the identity extends from the dense submodule of tests.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The integral of a product of two `L²` functions is their inner product (real case). -/
theorem integral_mul_eq_inner_L2 (a b : PlaneL2) :
    ∫ x, a x * b x = inner ℝ a b := by
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  simp [RCLike.inner_apply, mul_comm]

/-- The identity on a pair of test-supported `L²` representatives. -/
theorem testPair_transpose (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2))
    (hT : ∀ i k, ExtendsRieszTest (T i k) i k) (i k : Fin 2)
    (f g : Pl → ℝ) (hf : IsTest f) (hg : IsTest g) (h1 : MemLp f 2 volume) (h2 : MemLp g 2 volume) :
    ∫ x, T i k (h1.toLp f) x * (h2.toLp g) x = ∫ x, (h1.toLp f) x * T k i (h2.toLp g) x := by
  have eT1 : T i k (h1.toLp f) = (rieszTestMemLp i k f hf).toLp (rieszTest i k f) :=
    hT i k f hf h1 (rieszTestMemLp i k f hf)
  have eT2 : T k i (h2.toLp g) = (rieszTestMemLp k i g hg).toLp (rieszTest k i g) :=
    hT k i g hg h2 (rieszTestMemLp k i g hg)
  rw [eT1, eT2]
  have hS := rieszTestSymm i k f g hf hg
  have hC := rieszTestComm i k g hg
  rw [hC] at hS
  calc ∫ x, ((rieszTestMemLp i k f hf).toLp (rieszTest i k f)) x * (h2.toLp g) x
      = ∫ x, rieszTest i k f x * g x := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (rieszTestMemLp i k f hf), MemLp.coeFn_toLp h2] with x hx1 hx2
        rw [hx1, hx2]
    _ = ∫ x, f x * rieszTest k i g x := hS
    _ = ∫ x, (h1.toLp f) x * ((rieszTestMemLp k i g hg).toLp (rieszTest k i g)) x := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp h1, MemLp.coeFn_toLp (rieszTestMemLp k i g hg)] with x hx1 hx2
        rw [hx1, hx2]

/-- **Leaf `PartII-b:T12/1/1/2/46`.**  `∫ S_{ik} f · g = ∫ f · S_{ki} g` on `L²`. -/
theorem rieszL2Transpose : UnforcedLeray.Short.IIb.PlaneRiesz.RieszL2Transpose := by
  intro T hT i k f g
  obtain ⟨M, hM1, _, hMd⟩ := planeTestSub
  -- the defect `P (f, g) = ⟪T_{ik} f, g⟫ - ⟪f, T_{ki} g⟫` is continuous and bilinear
  let P : PlaneL2 × PlaneL2 → ℝ := fun p =>
    inner ℝ (T i k p.1) p.2 - inner ℝ p.1 (T k i p.2)
  have hPc : Continuous P := by
    have c1 : Continuous fun p : PlaneL2 × PlaneL2 => T i k p.1 :=
      (T i k).continuous.comp continuous_fst
    have c2 : Continuous fun p : PlaneL2 × PlaneL2 => T k i p.2 :=
      (T k i).continuous.comp continuous_snd
    exact (c1.inner continuous_snd).sub (continuous_fst.inner c2)
  have hsub : (M ×ˢ M : Set (PlaneL2 × PlaneL2)) ⊆ {p | P p = 0} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨f', hf', h1, rfl⟩ := hM1 a ha
    obtain ⟨g', hg', h2, rfl⟩ := hM1 b hb
    show inner ℝ (T i k (h1.toLp f')) (h2.toLp g') - inner ℝ (h1.toLp f') (T k i (h2.toLp g')) = 0
    rw [← integral_mul_eq_inner_L2, ← integral_mul_eq_inner_L2]
    exact sub_eq_zero.mpr (testPair_transpose T hT i k f' g' hf' hg' h1 h2)
  have hclosed : IsClosed {p : PlaneL2 × PlaneL2 | P p = 0} :=
    isClosed_eq hPc continuous_const
  have hall : closure (M ×ˢ M : Set (PlaneL2 × PlaneL2)) ⊆ {p | P p = 0} :=
    closure_minimal hsub hclosed
  have hdense : Dense (M ×ˢ M : Set (PlaneL2 × PlaneL2)) := hMd.prod hMd
  have hfg : (f, g) ∈ closure (M ×ˢ M : Set (PlaneL2 × PlaneL2)) := by
    rw [hdense.closure_eq]
    trivial
  have h0 : inner ℝ (T i k f) g - inner ℝ f (T k i g) = 0 := hall hfg
  rw [← integral_mul_eq_inner_L2, ← integral_mul_eq_inner_L2] at h0
  exact sub_eq_zero.mp h0

end UnforcedLeray.Short.IIb.PlaneRiesz
