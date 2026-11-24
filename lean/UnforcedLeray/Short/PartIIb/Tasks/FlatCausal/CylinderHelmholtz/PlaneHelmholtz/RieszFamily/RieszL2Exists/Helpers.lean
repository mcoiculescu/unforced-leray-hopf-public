import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestLinear
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestL2Bound

/-!
# Helpers for `PartII-b:T12/1/1/2/43` (`rieszL2Exists`)

Source of record: `the November 2 reference manuscript`, line 1670 and lines
1923-1926; Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

For a planar test `f`, `rl2Phi i k f hf` is the `L²` class of `S_{ik} f`.  The map `f ↦ rl2Phi`
is additive and homogeneous on tests, and depends only on the `L²` class of `f`
(`rl2_phi_eq`), which is what makes the extension to `PlaneL2` well defined.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- A test function is in `L²`. -/
theorem rl2_memLp {f : Pl → ℝ} (hf : IsTest f) : MemLp f 2 volume :=
  hf.1.continuous.memLp_of_hasCompactSupport hf.2

theorem rl2_isTest_add {f g : Pl → ℝ} (hf : IsTest f) (hg : IsTest g) : IsTest (f + g) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem rl2_isTest_sub {f g : Pl → ℝ} (hf : IsTest f) (hg : IsTest g) : IsTest (f - g) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem rl2_isTest_smul (c : ℝ) {f : Pl → ℝ} (hf : IsTest f) : IsTest (c • f) :=
  ⟨hf.1.const_smul c, hf.2.smul_left (f := fun _ : Pl => c)⟩

/-- Equal functions have equal `L²` classes, whatever the membership proofs. -/
theorem rl2_toLp_fun_eq {a b : Pl → ℝ} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume)
    (h : a = b) : ha.toLp a = hb.toLp b := by
  subst h
  rfl

/-- The `L²` class of `S_{ik} f` for a planar test `f`. -/
def rl2Phi (i k : Fin 2) (f : Pl → ℝ) (hf : IsTest f) : PlaneL2 :=
  (rieszTestMemLp i k f hf).toLp (rieszTest i k f)

/-- The `L²` class of `S_{ik} f` depends only on the `L²` class of `f`. -/
theorem rl2_phi_eq (i k : Fin 2) {f f' : Pl → ℝ} (hf : IsTest f) (hf' : IsTest f')
    (h : MemLp f 2 volume) (h' : MemLp f' 2 volume) (e : h.toLp f = h'.toLp f') :
    rl2Phi i k f hf = rl2Phi i k f' hf' := by
  have hd : IsTest (f - f') := rl2_isTest_sub hf hf'
  have h0 : (h.sub h').toLp (f - f') = 0 := by
    rw [MemLp.toLp_sub h h', e, sub_self]
  have hRd := rieszTestMemLp i k (f - f') hd
  have hb := rieszTestL2Bound i k (f - f') hd (h.sub h') hRd
  rw [h0, norm_zero] at hb
  have hz : hRd.toLp (rieszTest i k (f - f')) = 0 := norm_le_zero_iff.1 hb
  have hae : rieszTest i k (f - f') =ᵐ[volume] (0 : Pl → ℝ) := by
    have h1 := hRd.coeFn_toLp
    rw [hz] at h1
    exact h1.symm.trans (Lp.coeFn_zero _ _ _)
  have hlin : rieszTest i k f = rieszTest i k f' + rieszTest i k (f - f') := by
    have e2 : f' + (f - f') = f := by abel
    have := (rieszTestLinear i k f' (f - f') hf' hd 0).1
    rwa [e2] at this
  unfold rl2Phi
  rw [MemLp.toLp_eq_toLp_iff]
  filter_upwards [hae] with x hx
  rw [hlin]
  simp [hx]

/-- Additivity of `f ↦ S_{ik} f` on tests, at the level of `L²` classes. -/
theorem rl2_phi_add (i k : Fin 2) {f g : Pl → ℝ} (hf : IsTest f) (hg : IsTest g) :
    rl2Phi i k (f + g) (rl2_isTest_add hf hg) = rl2Phi i k f hf + rl2Phi i k g hg := by
  have e := (rieszTestLinear i k f g hf hg 0).1
  exact (rl2_toLp_fun_eq (rieszTestMemLp i k (f + g) (rl2_isTest_add hf hg))
    ((rieszTestMemLp i k f hf).add (rieszTestMemLp i k g hg)) e).trans
    (MemLp.toLp_add (rieszTestMemLp i k f hf) (rieszTestMemLp i k g hg))

/-- Homogeneity of `f ↦ S_{ik} f` on tests, at the level of `L²` classes. -/
theorem rl2_phi_smul (i k : Fin 2) (c : ℝ) {f : Pl → ℝ} (hf : IsTest f) :
    rl2Phi i k (c • f) (rl2_isTest_smul c hf) = c • rl2Phi i k f hf := by
  have e := (rieszTestLinear i k f f hf hf c).2
  exact (rl2_toLp_fun_eq (rieszTestMemLp i k (c • f) (rl2_isTest_smul c hf))
    ((rieszTestMemLp i k f hf).const_smul c) e).trans
    (MemLp.toLp_const_smul c (rieszTestMemLp i k f hf))

end UnforcedLeray.Short.IIb.PlaneRiesz
