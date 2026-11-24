import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# The positive-kernel estimate for the far part (source 3996-4014, 3611-3621, 3888-3897)

Source of record: `the November 2 reference manuscript`.

Route of the source (3996-4005, "by the same positive-kernel estimate", 4011-4014):

1. the pointwise majorant: by `sep:kernel` (3604-3610) the heat-Leray stress kernel has the
   positive majorant `C|x|^{-4}`, so `|farOut| ≤ C s^{-1/2} · farMajE` (`FarPointwiseMajorant`);
2. the source radius is separated from the output radius by a fixed multiple of `R/√s`, also after
   the source contraction `l ∈ (0,1)` in the resolvent (`FarSeparation`, 3997-3998);
3. the spatial `L¹` norm of `|x|^{-4}` outside distance `d` is `C/d` (`TailL1`, 3999-4000);
4. the exact dilation integral on an `L²` source has power `l^{2 Re μ + 1/2}`, hence a uniform
   integrability margin (`DilationMargin`, 4000-4001);
5. Young's inequality for the dilated positive kernel (`YoungDilated`), followed by the
   normalized-phase Minkowski inequality (`PhaseMinkowski`), gives `P_ν ε √r` (4002-4003);
   the bookkeeping on the chart is `FarMajorantL2`.

`FarSeparation`, `TailL1`, `DilationMargin`, `YoungDilated`, `PhaseMinkowski` are generic and are
reusable by the strip estimate `StripKernelBound` (same route).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The positive majorant of the masked far kernel (source 3996-4003, 3905-3912): at the chart
point `x` (output age `s = x.1`),
`∫_0^1 l^{2μ+2} ∫ |y - l z|^{-4} 1_{e^δ s < t(z)} |𝒩_T f(τ + 2 log l, z)| dz dl` with
`(y, τ) = (chartY R x, chartTau R x)`, in `[0,∞]`. -/
def farMajE (R c δ μ : ℝ) (f : Chart → Ten3) (x : Chart) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
    ∫⁻ z : UnforcedLeray.Space,
      if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
        ENNReal.ofReal (‖chartY R x - l • z‖ ^ (-4 : ℝ)) *
          UnforcedLeray.Short.IIIa.srcNorm (cartLift R c f) (chartTau R x + 2 * Real.log l) z
      else 0

/-- **Step 1: the pointwise majorant** (source 3611-3621, 3604-3610): from `SepKernelBounds`
(`j = 0`), `|farOut| ≤ C s^{-1/2} farMajE`, with `C` independent of all parameters. -/
def FarPointwiseMajorant : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (R c ν δ S μ : ℝ), 0 < ν → ∀ (f : Chart → Ten3) (x : Chart),
    ‖farOut R c ν μ δ S f x‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMajE R c δ μ f x)

/-- **Step 2: separation** (source 3997-3998, "separated from the output radius by a fixed
multiple of `R/√r`, also after the source contraction"): if `|y'| = R/√s`, the mask
`e^δ s < R²/|z'|²` holds and `l ∈ (0,1)`, then `|y - l z| ≥ (1 - e^{-δ/2}) R/√s`. -/
def FarSeparation : Prop :=
  ∀ (R δ s : ℝ), 0 < R → 0 < δ → 0 < s → ∀ y z : UnforcedLeray.Space, ∀ l : ℝ,
    0 < l → l < 1 → hRad y = R / Real.sqrt s → Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) →
      (1 - Real.exp (-δ / 2)) * (R / Real.sqrt s) ≤ ‖y - l • z‖

/-- **Step 3: the `L¹` tail** (source 3999-4000, "spatial `L¹` norm outside distance `d` is
`C/d`"): `∫_{|x| ≥ d} |x|^{-4} dx ≤ C/d` on `ℝ³`. -/
def TailL1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d →
    ∫⁻ x in {x : UnforcedLeray.Space | d ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ (-4 : ℝ)) ≤
      ENNReal.ofReal (C / d)

/-- **Step 4: the dilation margin** (source 4000-4001, "power `λ^{2 Re μ + 1/2}` ... uniform
integrability margin"): uniformly on a compact `K ⊆ (0, 1/4)`, `∫_0^1 l^{2μ+1/2} dl ≤ C`. -/
def DilationMargin : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ ∈ Kset,
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) ≤ ENNReal.ofReal C

/-- **Step 5a: Young for the dilated positive kernel** (source 4001-4002): for a measurable
`k ≥ 0` on `ℝ³` with `∫ k ≤ A`, `l > 0` and measurable `g ≥ 0`,
`‖∫ k(y - l z) g(z) dz‖_{L²_y} ≤ l^{-3/2} A ‖g‖_{L²}` (the power `l^{-3/2}` combines with the
weight `l^{2μ+2}` to the exponent `2μ + 1/2` of `DilationMargin`). -/
def YoungDilated : Prop :=
  ∀ (k g : UnforcedLeray.Space → ℝ≥0∞), Measurable k → Measurable g →
    ∀ A : ℝ≥0∞, ∫⁻ x, k x ≤ A → ∀ l : ℝ, 0 < l →
      (∫⁻ y : UnforcedLeray.Space,
          (∫⁻ z : UnforcedLeray.Space, k (y - l • z) * g z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * A * (∫⁻ z, g z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- **Step 5b: Minkowski's integral inequality** (source 4002, "normalized-phase Minkowski"), in
`L²` of a general measure (used over `(y, τ)`): for jointly measurable `F ≥ 0` and measurable
`S ⊆ ℝ`, `‖∫_S F(l, ·) dl‖_{L²(ν)} ≤ ∫_S ‖F(l, ·)‖_{L²(ν)} dl`. -/
def PhaseMinkowski : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) [SFinite ν] (F : ℝ → α → ℝ≥0∞),
    Measurable (Function.uncurry F) → ∀ S : Set ℝ, MeasurableSet S →
      (∫⁻ a, (∫⁻ l in S, F l a) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ≤
        ∫⁻ l in S, (∫⁻ a, F l a ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)

/-- **The `L²` bound of the positive majorant on the chart** (source 3996-4014: the steps 2-5
assembled, `C/d` with `d = (1 - e^{-δ/2}) R/√s₋ = c_δ ε⁻¹ s₋^{-1/2}` giving the factor `ε√s₋`):
for `s₋ ≤ S` and a box tensor `f` supported in `t < e^δ s₋`,
`‖1_{s<s₋} s^{-1/2} farMajE‖_{L²(ageμ(-3/2))} ≤ P_ν ε√s₋ ‖f‖_{L²(ageμ(-1/2))}`. -/
def FarMajorantL2 : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ Kset, ∀ sm : ℝ, 0 < sm → sm ≤ p.ε ^ (-b) →
      ∀ f : Chart → Ten3, IsBoxTensor f → (∀ x, f x ≠ 0 → x.1 < Real.exp δ * sm) →
        (∫⁻ x in ageBelow sm,
            (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMajE p.R p.c δ μ f x) ^ (2 : ℝ)
              ∂(ageμ p.c (-3 / 2))) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) * eLpNorm f 2 (ageμ p.c (-1 / 2))

/-- **Assembly**: the forbidden kernel estimate from the pointwise majorant and the `L²` bound of
the majorant. -/
theorem forbiddenKernelBound_of_sub (hA : FarPointwiseMajorant) (hB : FarMajorantL2) :
    ForbiddenKernelBound := by
  obtain ⟨CA, hCA, hA⟩ := hA
  intro Kset hK hKs dm dp hdm b δ hb hb1 hδ
  obtain ⟨CB, k, ν₀, hν₀, hB⟩ := hB Kset hK hKs dm dp hdm b δ hb hb1 hδ
  refine ⟨CA * CB, k, ν₀, hν₀, ?_⟩
  intro p d hreg hν μ hμ sm hsm hsS f hf hsupp
  have hBB := hB p d hreg hν μ hμ sm hsm hsS f hf hsupp
  have hmeas : MeasurableSet (ageBelow sm) :=
    measurableSet_lt measurable_fst measurable_const
  set G : Chart → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMajE p.R p.c δ μ f x with hG
  have hpt : ∀ x, ‖(ageBelow sm).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) f) x‖ₑ ≤
      ENNReal.ofReal CA * (ageBelow sm).indicator G x := by
    intro x
    by_cases hx : x ∈ ageBelow sm
    · simp only [Set.indicator_of_mem hx]
      exact hA p.R p.c p.ν δ (p.ε ^ (-b)) μ p.ν_pos f x
    · simp [Set.indicator_of_notMem hx]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]
  have hind : ∫⁻ x, ((ageBelow sm).indicator G x) ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2)) =
      ∫⁻ x in ageBelow sm, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2)) := by
    rw [← lintegral_indicator hmeas]
    congr 1
    ext x
    by_cases hx : x ∈ ageBelow sm
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have step1 : ∫⁻ x, ‖(ageBelow sm).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) f) x‖ₑ ^ (2 : ℝ)
        ∂(ageμ p.c (-3 / 2)) ≤
      ENNReal.ofReal CA ^ (2 : ℝ) *
        ∫⁻ x in ageBelow sm, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2)) := by
    rw [← hind, ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow (hpt x) (by norm_num)
  calc (∫⁻ x, ‖(ageBelow sm).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) f) x‖ₑ ^ (2 : ℝ)
        ∂(ageμ p.c (-3 / 2))) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal CA ^ (2 : ℝ) *
          ∫⁻ x in ageBelow sm, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow step1 (by norm_num)
    _ = ENNReal.ofReal CA *
          (∫⁻ x in ageBelow sm, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2))) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
    _ ≤ ENNReal.ofReal CA * (ENNReal.ofReal (CB * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) *
          eLpNorm f 2 (ageμ p.c (-1 / 2))) := by
        gcongr
    _ = ENNReal.ofReal (CA * CB * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) *
          eLpNorm f 2 (ageμ p.c (-1 / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCA]
        congr 2
        ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
