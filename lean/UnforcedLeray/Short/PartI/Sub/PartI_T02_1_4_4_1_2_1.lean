import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2
import UnforcedLeray.Lib.SobolevC.CylTransfer

/-!
# Part I, `PartI:T02/1/4/4/1/2/1`: the weak product rule `∂_j (a u) = a' u + a u'` on the cylinder

Source of record: `the November 2 reference manuscript`, lines 261-288
(the weak Leibniz rule for the advection term on the cell, for the `H^1` product estimate).

Reduction of `CylWeakProductSmul` (`PartI_T02_1_4_4_1_2.lean`) to two statements on `ℝ²`/the
cylinder, through the periodic extension `perExt` of `Lib/SobolevC/CylExtend.lean`:

* `PerExtCylBack`: a periodic weak derivative on `ℝ²` of the periodic extensions of fields that are
  integrable on every strip `cell ∩ {|η| ≤ M}` is a periodic weak derivative on the cylinder (the
  converse of `Sob.hasWeakDeriv_perExt`, by unfolding a cylinder test as the periodization
  `perSum c χ` of a compactly supported test);
* `PlaneProductSmul`: the weak product rule for a scalar times a vector on `ℝ²`, for locally `L²`
  factors (the local form of `Sob.HasWeakDeriv.bilin`, `Lib/SobolevB/Bilin.lean`, by a cutoff).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Unfolding of cylinder tests.**  Every cylinder test `φ` is the periodization
`perSum c χ` of a smooth compactly supported `χ` on `ℝ²`
(`χ = φ · β`, with `β` a smooth compactly supported function of `q` whose periodization is `1`,
e.g. `β = b / perSum c b` for a bump `b` positive on `[-c/2, c/2]`;
`perSum c (φ β) = φ · perSum c β` by periodicity of `φ`). -/
def CylTestUnfold : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ φ : ℝ × ℝ → ℝ, Sob.IsCylTest c φ →
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ ∀ z, Sob.perSum c χ z = φ z

/-- **Back from `ℝ²` to the cylinder** (converse of `Sob.hasWeakDeriv_perExt`, source lines 261-288):
for fields integrable on every strip, the weak derivative identity of the periodic extensions on
`ℝ²` against compactly supported tests gives the periodic weak derivative on the cylinder.
Proof idea: for a cylinder test `φ` take `χ` from `CylTestUnfold`, so `iterDirDeriv vs φ =
perSum c (iterDirDeriv vs χ)` (`Sob.iterDirDeriv_perSum`), and use `Sob.integral_smul_perExt` on
both sides to unfold the cell integrals; the two integrabilities on the cell come from the
`.1` parts of `Sob.integral_smul_perExt` together with the `hasWeakDeriv`-integrability clauses
(or directly: `φ` is bounded on `cell ∩ {|η| ≤ R}` and vanishes outside). -/
def PerExtCylBack : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (vs : List (ℝ × ℝ)) (f g : ℝ × ℝ → Cyl.Vec2),
    MeasureTheory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable g →
    (∀ M : ℝ, IntegrableOn f (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M})) →
    (∀ M : ℝ, IntegrableOn g (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M})) →
    Sob.HasWeakDeriv (Sob.wholeSpaceOf (ℝ × ℝ) volume Sob.cylDir) vs
      (Sob.perExt hc f) (Sob.perExt hc g) →
    Sob.HasWeakDeriv (Sob.cylinder c) vs f g

/-- **Local weak product rule on `ℝ²`** for a scalar times a vector (source lines 261-288):
if `f, f', g, g'` are `L²` on every box and `f' = ∂_{cylDir j} f`, `g' = ∂_{cylDir j} g` weakly
(tests `C_c^∞(ℝ²)`), then `∂_{cylDir j}(f g) = f' g + f g'` weakly.  Proof idea: multiply by a
smooth cutoff `θ = 1` near the support of the test function (scalar Leibniz
`Sob.HasWeakDeriv.smul_left`), so `θ f, θ g ∈ L²(ℝ²)`; transfer along `Sob.toPlane`
(`Sob.hasWeakDeriv_comp_toPlane`, `toPlane_symm_cylDir`) and apply `Sob.HasWeakDeriv.bilin`
(`p = q = 2`, `r = 1`, `B = ` scalar multiplication); on the support of the test `θ = 1`,
`∇θ = 0`. -/
def PlaneProductSmul : Prop :=
  ∀ (j : Fin 2) (f f' : ℝ × ℝ → ℝ) (g g' : ℝ × ℝ → Cyl.Vec2),
    (∀ A M : ℝ, MemLp f 2 (volume.restrict (Icc (-A) A ×ˢ Icc (-M) M))) →
    (∀ A M : ℝ, MemLp f' 2 (volume.restrict (Icc (-A) A ×ˢ Icc (-M) M))) →
    (∀ A M : ℝ, MemLp g 2 (volume.restrict (Icc (-A) A ×ˢ Icc (-M) M))) →
    (∀ A M : ℝ, MemLp g' 2 (volume.restrict (Icc (-A) A ×ˢ Icc (-M) M))) →
    Sob.HasWeakDeriv (Sob.wholeSpaceOf (ℝ × ℝ) volume Sob.cylDir) [Sob.cylDir j] f f' →
    Sob.HasWeakDeriv (Sob.wholeSpaceOf (ℝ × ℝ) volume Sob.cylDir) [Sob.cylDir j] g g' →
    Sob.HasWeakDeriv (Sob.wholeSpaceOf (ℝ × ℝ) volume Sob.cylDir) [Sob.cylDir j]
      (fun z => f z • g z) (fun z => f' z • g z + f z • g' z)

namespace CylProd

/-- A field in `L²(cell)` is `L²` on every strip `cell ∩ {|η| ≤ M}`. -/
theorem memLp_strip {c : ℝ} {E : Type*} [NormedAddCommGroup E]
    {h : ℝ × ℝ → E} (hh : MemLp h 2 (volume.restrict (Sob.cylCell c))) (M : ℝ) :
    MemLp h 2 (volume.restrict (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M})) :=
  hh.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)

theorem finite_strip (c M : ℝ) :
    IsFiniteMeasure (volume.restrict (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M})) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono (Sob.cylCell_subset_box c M))
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top

theorem integrableOn_strip {c : ℝ} {E : Type*} [NormedAddCommGroup E] {h : ℝ × ℝ → E}
    (hh : MemLp h 2 (volume.restrict (Sob.cylCell c))) (M : ℝ) :
    IntegrableOn h (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M}) := by
  haveI := finite_strip c M
  exact (memLp_strip hh M).integrable (by norm_num)

theorem integrableOn_strip1 {c : ℝ} {E : Type*} [NormedAddCommGroup E] {h : ℝ × ℝ → E}
    (hh : MemLp h 1 (volume.restrict (Sob.cylCell c))) (M : ℝ) :
    IntegrableOn h (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M}) :=
  (memLp_one_iff_integrable.1 hh).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)

theorem memLp_box {c : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ × ℝ → E}
    (hs : StronglyMeasurable h) (hh : MemLp h 2 (volume.restrict (Sob.cylCell c))) (A M : ℝ) :
    MemLp (Sob.perExt hc h) 2 (volume.restrict (Icc (-A) A ×ˢ Icc (-M) M)) :=
  Sob.memLp_box_perExt hc (by norm_num) (by norm_num) hs (fun M => (memLp_strip hh M).2) A M

theorem memLp_smul_strip {c : ℝ} {f : ℝ × ℝ → ℝ} {g : ℝ × ℝ → Cyl.Vec2}
    (hf : MemLp f 2 (volume.restrict (Sob.cylCell c)))
    (hg : MemLp g 2 (volume.restrict (Sob.cylCell c))) :
    MemLp (fun z => f z • g z) 1 (volume.restrict (Sob.cylCell c)) := by
  haveI : ENNReal.HolderTriple 2 2 1 := inferInstance
  exact hg.smul hf

end CylProd

open CylProd in
theorem cylWeakProductSmul_of (h1 : PerExtCylBack) (h2 : PlaneProductSmul) :
    CylWeakProductSmul := by
  intro c j a a' u u' ha ha' hu hu' hwa hwu
  rcases le_or_gt c 0 with hc | hc
  · have h0 : (Sob.cylinder c).μ = 0 := by
      rw [Sob.cylinder_μ, Sob.cylCell_eq_empty hc, Measure.restrict_empty]
    refine ⟨fun φ _ => ?_, fun φ _ => ?_, fun φ _ => ?_⟩
    · rw [h0]; exact integrable_zero_measure
    · rw [h0]; exact integrable_zero_measure
    · rw [h0]; simp
  have hμ : Cyl.cellμ c = volume.restrict (Sob.cylCell c) := by
    rw [← Cyl.cylinder_μ_eq]; rfl
  have hμ' : (Sob.cylinder c).μ = volume.restrict (Sob.cylCell c) := rfl
  rw [hμ] at ha ha' hu hu'
  -- strongly measurable representatives
  set a1 := ha.1.mk a with ha1
  set a1' := ha'.1.mk a' with ha1'
  set u1 := hu.1.mk u with hu1
  set u1' := hu'.1.mk u' with hu1'
  have ea : a =ᵐ[(Sob.cylinder c).μ] a1 := by rw [hμ']; exact ha.1.ae_eq_mk
  have ea' : a' =ᵐ[(Sob.cylinder c).μ] a1' := by rw [hμ']; exact ha'.1.ae_eq_mk
  have eu : u =ᵐ[(Sob.cylinder c).μ] u1 := by rw [hμ']; exact hu.1.ae_eq_mk
  have eu' : u' =ᵐ[(Sob.cylinder c).μ] u1' := by rw [hμ']; exact hu'.1.ae_eq_mk
  have sa : StronglyMeasurable a1 := ha.1.stronglyMeasurable_mk
  have sa' : StronglyMeasurable a1' := ha'.1.stronglyMeasurable_mk
  have su : StronglyMeasurable u1 := hu.1.stronglyMeasurable_mk
  have su' : StronglyMeasurable u1' := hu'.1.stronglyMeasurable_mk
  have la : MemLp a1 2 (volume.restrict (Sob.cylCell c)) := ha.ae_eq ha.1.ae_eq_mk
  have la' : MemLp a1' 2 (volume.restrict (Sob.cylCell c)) := ha'.ae_eq ha'.1.ae_eq_mk
  have lu : MemLp u1 2 (volume.restrict (Sob.cylCell c)) := hu.ae_eq hu.1.ae_eq_mk
  have lu' : MemLp u1' 2 (volume.restrict (Sob.cylCell c)) := hu'.ae_eq hu'.1.ae_eq_mk
  have wa := hwa.congr_ae ea ea'
  have wu := hwu.congr_ae eu eu'
  -- the plane weak derivatives of the periodic extensions
  have pa := Sob.hasWeakDeriv_perExt hc sa sa' (integrableOn_strip la) (integrableOn_strip la') wa
  have pu := Sob.hasWeakDeriv_perExt hc su su' (integrableOn_strip lu) (integrableOn_strip lu') wu
  have pp := h2 j _ _ _ _ (memLp_box hc sa la) (memLp_box hc sa' la') (memLp_box hc su lu)
    (memLp_box hc su' lu') pa pu
  have P1 := memLp_smul_strip la lu
  have P2 := memLp_smul_strip la' lu
  have P3 := memLp_smul_strip la lu'
  have P23 : MemLp (fun z => a1' z • u1 z + a1 z • u1' z) 1 (volume.restrict (Sob.cylCell c)) :=
    P2.add P3
  have back := h1 c hc [Sob.cylDir j] (fun z => a1 z • u1 z)
    (fun z => a1' z • u1 z + a1 z • u1' z) (sa.smul su) ((sa'.smul su).add (sa.smul su'))
    (fun M => integrableOn_strip1 P1 M)
    (fun M => integrableOn_strip1 P23 M) pp
  refine back.congr_ae ?_ ?_
  · filter_upwards [ea, eu] with z h1 h2
    simp only [h1, h2]
  · filter_upwards [ea, eu, ea', eu'] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4]

end UnforcedLeray.Short.PartI
