import UnforcedLeray.Lib.CylinderB.Space
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# CY09: periodization, unfolding and convolution on the cell


(§5 Layer 1; bypass BP1). Manuscript: `paper/main.tex` lines 6037–6045 (B0314, the horizontal
periodization `(P_c f)(q,η) = Σ_n f(q − nc, η)`), 6788–6801 (B0364(b): the cell integral of a
periodization equals the whole-plane integral), and the cell contraction of planar convolutions
used for the cylinder heat and the mollifier (decision D1: "the cylinder heat becomes the planar
heat applied to periodic functions, with the cell contraction from CY09").

## Main declarations
* `periodize c f`, `isPeriodic_periodize`;
* `zmultiplesEquiv`: `ℤ ≃ ℤ·(c,0)`;
* `lintegral_cell_periodize`: `∫⁻_cell Σ_n f(q − nc, η) = ∫⁻_{ℝ²} f` (unfolding, `[0,∞]`-valued);
* `integral_cell_periodize_mul`: `∫_cell (P_c f) g = ∫_{ℝ²} f g` for periodic `g` and integrable
  `f g` (B0364(b));
* `eLpNorm_conv_periodic_le`: `‖∫ k(y) f(· − y) dν(y)‖_{Lᵖ(cell)} ≤ (∫ |k| dν) ‖f‖_{Lᵖ(cell)}` for
  periodic `f`, every `s`-finite `ν` (Minkowski plus translation invariance of the cell norm);
  its instances `eLpNorm_planarConv_periodic_le` (`ν` = Lebesgue measure on `ℝ²`) and
  `eLpNorm_cellConv_le` (`ν` = Lebesgue measure on the cell);
* `norm_conv_periodic_le_sup`: `‖∫_cell k(y) f(x − y) dy‖ ≤ (sup |k|) ‖f‖_{L¹(cell)}`.

Junk values: `periodize` is a `tsum`, which is `0` when the series does not converge; the
unfolding identities hold without any summability hypothesis because they are stated for
`[0,∞]`-valued functions or pass through `tsum_mul_right` and `integral_tsum`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace UnforcedLeray.Cyl

/-- **Horizontal periodization** `(P_c f)(q,η) = Σ_{n ∈ ℤ} f(q − nc, η)` (B0314, tex 6037–6045). -/
def periodize {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (c : ℝ) (f : Plane → E)
    (z : Plane) : E :=
  ∑' n : ℤ, f (z.1 - n * c, z.2)

theorem isPeriodic_periodize {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (c : ℝ)
    (f : Plane → E) : IsPeriodic c (periodize c f) := by
  intro z
  simp only [periodize]
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  congr 1
  funext n
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  congr 2
  ring

/-- `n ↦ n • (c, 0)` identifies `ℤ` with the period lattice. -/
def zmultiplesEquiv {c : ℝ} (hc : 0 < c) : ℤ ≃ AddSubgroup.zmultiples ((c, 0) : Plane) :=
  Equiv.ofBijective (fun n => ⟨n • ((c, 0) : Plane), n, rfl⟩) ⟨fun m n h => by
    have h' : m • ((c, 0) : Plane) = n • ((c, 0) : Plane) := congrArg Subtype.val h
    have h1 : (m : ℝ) * c = (n : ℝ) * c := by
      have := congrArg Prod.fst h'
      simpa [zsmul_eq_mul] using this
    exact_mod_cast mul_right_cancel₀ hc.ne' h1, fun g => by
      obtain ⟨g, n, rfl⟩ := g
      exact ⟨n, rfl⟩⟩

theorem zmultiplesEquiv_vadd {c : ℝ} (hc : 0 < c) (n : ℤ) (z : Plane) :
    (zmultiplesEquiv hc n) +ᵥ z = (z.1 + n * c, z.2) := by
  rw [AddSubgroup.vadd_def]
  show n • ((c, 0) : Plane) + z = _
  ext <;> simp [zsmul_eq_mul, add_comm]

/-- Unfolding along the lattice: `∫⁻_{ℝ²} f = Σ_n ∫⁻_cell f(q + nc, η)`. -/
theorem lintegral_eq_tsum_cell {c : ℝ} (hc : 0 < c) (f : Plane → ℝ≥0∞) :
    ∫⁻ z, f z = ∑' n : ℤ, ∫⁻ z in cell c, f (z.1 + n * c, z.2) := by
  rw [(isAddFundamentalDomain_cell hc).lintegral_eq_tsum'', ← (zmultiplesEquiv hc).tsum_eq]
  simp_rw [zmultiplesEquiv_vadd]

/-- Unfolding along the lattice, Bochner version. -/
theorem integral_eq_tsum_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 0 < c) {f : Plane → E} (hf : Integrable f) :
    ∫ z, f z = ∑' n : ℤ, ∫ z in cell c, f (z.1 + n * c, z.2) := by
  rw [(isAddFundamentalDomain_cell hc).integral_eq_tsum'' f hf, ← (zmultiplesEquiv hc).tsum_eq]
  simp_rw [zmultiplesEquiv_vadd]

theorem IsPeriodic.add_int_mul {E : Type*} {c : ℝ} {f : Plane → E} (hf : IsPeriodic c f)
    (n : ℤ) (z : Plane) : f (z.1 + n * c, z.2) = f z := by
  rw [← zsmul_eq_mul]; exact hf.add_zsmul n z

theorem measurable_shift (c : ℝ) (n : ℤ) : Measurable fun z : Plane => (z.1 - n * c, z.2) :=
  (measurable_fst.sub_const _).prodMk measurable_snd

theorem measurePreserving_shift (a : ℝ) :
    MeasurePreserving (fun z : Plane => (z.1 + a, z.2)) volume volume := by
  have : (fun z : Plane => (z.1 + a, z.2)) = fun z => z + ((a, 0) : Plane) := by
    funext z; ext <;> simp
  rw [this]
  exact measurePreserving_add_right volume _

/-- **Unfolding** (B0364(b), `[0,∞]`-valued): `∫⁻_cell Σ_n f(q − nc, η) = ∫⁻_{ℝ²} f`. -/
theorem lintegral_cell_periodize {c : ℝ} (hc : 0 < c) {f : Plane → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in cell c, periodize c f z = ∫⁻ z, f z := by
  rw [lintegral_eq_tsum_cell hc]
  simp only [periodize]
  rw [lintegral_tsum (f := fun (n : ℤ) (z : Plane) => f (z.1 - n * c, z.2))
    fun n => (hf.comp (measurable_shift c n)).aemeasurable]
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext n
  congr 1
  funext z
  simp [sub_eq_add_neg]

/-- **Unfolding** (B0364(b), tex 6788–6801): for `c`-periodic `g` and integrable `f g`,
`∫_cell (P_c f) g = ∫_{ℝ²} f g`. No summability of `P_c f` is assumed: the left side is
evaluated through `tsum_mul_right`. -/
theorem integral_cell_periodize_mul {𝕜 : Type*} [RCLike 𝕜] {c : ℝ} (hc : 0 < c)
    {f g : Plane → 𝕜} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hper : IsPeriodic c g) (hfg : Integrable fun z => f z * g z) :
    ∫ z in cell c, periodize c f z * g z = ∫ z, f z * g z := by
  have hL : ∀ z, periodize c f z * g z = ∑' n : ℤ, f (z.1 - n * c, z.2) * g z := by
    intro z
    rw [periodize, tsum_mul_right]
  simp_rw [hL]
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (fun z => f (z.1 - n * c, z.2) * g z)
      (volume.restrict (cell c)) := fun n =>
    ((hf.comp_measurable (measurable_shift c n)).mul hg).aestronglyMeasurable
  have harg : ∀ (n : ℤ) (z : Plane), ((z.1 - n * c, z.2) : Plane) = (z.1 + ((-n : ℤ) : ℝ) * c, z.2) :=
    fun n z => Prod.ext (by push_cast; ring) rfl
  have hpt : ∀ (n : ℤ) (z : Plane), f (z.1 - n * c, z.2) * g z =
      (fun w => f w * g w) (z.1 + ((-n : ℤ) : ℝ) * c, z.2) := by
    intro n z
    simp only
    rw [hper.add_int_mul (-n) z, harg]
  have hsum : ∑' n : ℤ, ∫⁻ z in cell c, ‖f (z.1 - n * c, z.2) * g z‖ₑ ≠ ∞ := by
    have e1 : ∀ n : ℤ, ∫⁻ z in cell c, ‖f (z.1 - n * c, z.2) * g z‖ₑ =
        (fun m : ℤ => ∫⁻ z in cell c, ‖f (z.1 + m * c, z.2) * g (z.1 + m * c, z.2)‖ₑ) (-n) := by
      intro n
      simp only
      congr 1
      funext z
      rw [hpt n z]
    rw [tsum_congr e1]
    have h3 := (Equiv.neg ℤ).tsum_eq
      (fun m : ℤ => ∫⁻ z in cell c, ‖f (z.1 + m * c, z.2) * g (z.1 + m * c, z.2)‖ₑ)
    simp only [Equiv.neg_apply] at h3
    rw [h3, ← lintegral_eq_tsum_cell hc fun z => ‖f z * g z‖ₑ]
    exact hfg.2.ne
  rw [integral_tsum hmeas hsum, integral_eq_tsum_cell hc hfg]
  have e2 : ∀ n : ℤ, ∫ z in cell c, f (z.1 - n * c, z.2) * g z =
      (fun m : ℤ => ∫ z in cell c, f (z.1 + m * c, z.2) * g (z.1 + m * c, z.2)) (-n) := by
    intro n
    simp only
    congr 1
    funext z
    rw [hpt n z]
  rw [tsum_congr e2]
  have h3 := (Equiv.neg ℤ).tsum_eq
    (fun m : ℤ => ∫ z in cell c, f (z.1 + m * c, z.2) * g (z.1 + m * c, z.2))
  simp only [Equiv.neg_apply] at h3
  rw [h3]

/-! ### Convolution against periodic functions -/

section Conv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance sigmaFinite_cellμ (c : ℝ) : SigmaFinite (cellμ c) := by
  rw [cellμ]; infer_instance

omit [NormedSpace ℝ E] in
/-- The `Lᵖ(cell)` norm of a periodic function is translation invariant. -/
theorem eLpNorm_cell_comp_sub {c : ℝ} (hc : 0 < c) {f : Plane → E} (hper : IsPeriodic c f)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (y : Plane) :
    eLpNorm (fun x => f (x - y)) p (cellμ c) = eLpNorm f p (cellμ c) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  congr 1
  have hper' : IsPeriodic c fun z => ‖f z‖ₑ ^ p.toReal := fun z => by simp only [hper z]
  simp_rw [sub_eq_add_neg]
  exact lintegral_cell_comp_add hc hper' (-y)

/-- **Convolution on the cylinder** (CY09, Minkowski plus translation invariance): for a
`c`-periodic `f`, every `s`-finite measure `ν` on `ℝ²` and `1 ≤ p < ∞`,
`‖∫ k(y) f(· − y) dν(y)‖_{Lᵖ(cell)} ≤ (∫⁻ |k| dν) ‖f‖_{Lᵖ(cell)}`. -/
theorem eLpNorm_conv_periodic_le {c : ℝ} (hc : 0 < c) {ν : Measure Plane} [SigmaFinite ν]
    {k : Plane → ℝ} {f : Plane → E} (hk : StronglyMeasurable k) (hf : StronglyMeasurable f)
    (hper : IsPeriodic c f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => ∫ y, k y • f (x - y) ∂ν) p (cellμ c) ≤
      (∫⁻ y, ‖k y‖ₑ ∂ν) * eLpNorm f p (cellμ c) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hF : AEStronglyMeasurable (Function.uncurry fun x y => k y • f (x - y))
      ((cellμ c).prod ν) := by
    have : StronglyMeasurable (Function.uncurry fun (x : Plane) (y : Plane) => k y • f (x - y)) :=
      (hk.comp_measurable measurable_snd).smul
        (hf.comp_measurable (measurable_fst.sub measurable_snd))
    exact this.aestronglyMeasurable
  refine (UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le hF hp hp').trans (le_of_eq ?_)
  calc ∫⁻ y, eLpNorm (fun x => k y • f (x - y)) p (cellμ c) ∂ν
      = ∫⁻ y, ‖k y‖ₑ * eLpNorm f p (cellμ c) ∂ν := by
        congr 1
        funext y
        rw [show (fun x => k y • f (x - y)) = k y • (fun x => f (x - y)) from rfl,
          eLpNorm_const_smul, eLpNorm_cell_comp_sub hc hper hp0 hp' y]
    _ = (∫⁻ y, ‖k y‖ₑ ∂ν) * eLpNorm f p (cellμ c) :=
        lintegral_mul_const _ hk.measurable.enorm

/-- `eLpNorm_conv_periodic_le` for a planar kernel: `‖k ⋆ f‖_{Lᵖ(cell)} ≤ ‖k‖_{L¹(ℝ²)} ‖f‖_{Lᵖ(cell)}`
(heat semigroup and mollifiers on the cylinder, D1). -/
theorem eLpNorm_planarConv_periodic_le {c : ℝ} (hc : 0 < c) {k : Plane → ℝ} {f : Plane → E}
    (hk : StronglyMeasurable k) (hf : StronglyMeasurable f) (hper : IsPeriodic c f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => ∫ y, k y • f (x - y)) p (cellμ c) ≤
      eLpNorm k 1 volume * eLpNorm f p (cellμ c) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_conv_periodic_le hc hk hf hper hp hp'

/-- `eLpNorm_conv_periodic_le` for a kernel integrated over the cell:
`‖∫_cell k(y) f(· − y) dy‖_{Lᵖ(cell)} ≤ ‖k‖_{L¹(cell)} ‖f‖_{Lᵖ(cell)}`. -/
theorem eLpNorm_cellConv_le {c : ℝ} (hc : 0 < c) {k : Plane → ℝ} {f : Plane → E}
    (hk : StronglyMeasurable k) (hf : StronglyMeasurable f) (hper : IsPeriodic c f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => ∫ y in cell c, k y • f (x - y)) p (cellμ c) ≤
      eLpNorm k 1 (cellμ c) * eLpNorm f p (cellμ c) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_conv_periodic_le hc hk hf hper hp hp'

/-- The preimage of the cell under `y ↦ x - y` is, up to a null set, the period strip
starting at `x.1 - c/2`. -/
theorem preimage_sub_cell_ae_eq (c : ℝ) (x : Plane) :
    ((fun y => x - y) ⁻¹' cell c : Set Plane) =ᵐ[volume]
      (Ico (x.1 - c / 2) (x.1 - c / 2 + c) ×ˢ (univ : Set ℝ) : Set Plane) := by
  filter_upwards [Sob.ae_fst_ne (x.1 - c / 2), Sob.ae_fst_ne (x.1 + c / 2)] with w h1 h2
  change (w ∈ (fun y => x - y) ⁻¹' cell c) = (w ∈ Ico (x.1 - c / 2) (x.1 - c / 2 + c) ×ˢ univ)
  simp only [mem_preimage, mem_cell, Prod.fst_sub, mem_prod, mem_Ico, mem_univ, and_true,
    eq_iff_iff]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨?_, ?_⟩
    · by_contra h; push Not at h
      exact h1 (le_antisymm h.le (by linarith))
    · by_contra h; push Not at h
      exact h2 (le_antisymm (by linarith) (by linarith))
  · rintro ⟨ha, hb⟩
    refine ⟨?_, ?_⟩
    · by_contra h; push Not at h
      exact h2 (le_antisymm (by linarith) (by linarith))
    · by_contra h; push Not at h
      exact h1 (le_antisymm (by linarith) ha)

/-- **Reflection invariance** of cell integrals of periodic functions:
`∫_cell G(x − y) dy = ∫_cell G`. -/
theorem integral_cell_comp_sub_left {c : ℝ} (hc : 0 < c) {G : Plane → E} (hper : IsPeriodic c G)
    (x : Plane) : ∫ y in cell c, G (x - y) = ∫ y in cell c, G y := by
  have hmp : MeasurePreserving (fun y : Plane => x - y) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hemb : MeasurableEmbedding (fun y : Plane => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  have hset : (fun y : Plane => x - y) ⁻¹' ((fun y : Plane => x - y) ⁻¹' cell c) = cell c := by
    ext y; simp
  calc ∫ y in cell c, G (x - y)
      = ∫ y in (fun y : Plane => x - y) ⁻¹' ((fun y : Plane => x - y) ⁻¹' cell c), G (x - y) := by
        rw [hset]
    _ = ∫ w in (fun y : Plane => x - y) ⁻¹' cell c, G w := hmp.setIntegral_preimage_emb hemb _ _
    _ = ∫ w in Ico (x.1 - c / 2) (x.1 - c / 2 + c) ×ˢ (univ : Set ℝ), G w :=
        setIntegral_congr_set (preimage_sub_cell_ae_eq c x)
    _ = ∫ y in cell c, G y := integral_strip_eq_cell hc hper _

/-- **Reflection invariance**, `[0,∞]`-valued. -/
theorem lintegral_cell_comp_sub_left {c : ℝ} (hc : 0 < c) {G : Plane → ℝ≥0∞}
    (hper : IsPeriodic c G) (x : Plane) : ∫⁻ y in cell c, G (x - y) = ∫⁻ y in cell c, G y := by
  have hmp : MeasurePreserving (fun y : Plane => x - y) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hemb : MeasurableEmbedding (fun y : Plane => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  have hset : (fun y : Plane => x - y) ⁻¹' ((fun y : Plane => x - y) ⁻¹' cell c) = cell c := by
    ext y; simp
  calc ∫⁻ y in cell c, G (x - y)
      = ∫⁻ y in (fun y : Plane => x - y) ⁻¹' ((fun y : Plane => x - y) ⁻¹' cell c), G (x - y) := by
        rw [hset]
    _ = ∫⁻ w in (fun y : Plane => x - y) ⁻¹' cell c, G w :=
        hmp.setLIntegral_comp_preimage_emb hemb _ _
    _ = ∫⁻ w in Ico (x.1 - c / 2) (x.1 - c / 2 + c) ×ˢ (univ : Set ℝ), G w :=
        setLIntegral_congr (preimage_sub_cell_ae_eq c x)
    _ = ∫⁻ y in cell c, G y := lintegral_strip_eq_cell hc hper _

/-- The periodic cell convolution in the form `∫_cell f(y) k(x − y) dy` (the form of the
Biot–Savart operator `K_c ω`), rewritten as `∫_cell k(y) f(x − y) dy`. -/
theorem integral_cell_mul_comp_sub {c : ℝ} (hc : 0 < c) {k : Plane → ℝ} {f : Plane → E}
    (hk : IsPeriodic c k) (hf : IsPeriodic c f) (x : Plane) :
    ∫ y in cell c, k (x - y) • f y = ∫ y in cell c, k y • f (x - y) := by
  have hG : IsPeriodic c fun w => k w • f (x - w) := by
    intro w
    show k (w.1 + c, w.2) • f (x - (w.1 + c, w.2)) = k w • f (x - w)
    rw [hk w]
    congr 1
    have := hf.sub_eq (x - w)
    rw [← this]
    congr 1
    ext <;> simp; ring
  have := integral_cell_comp_sub_left hc hG x
  simpa using this

/-- **Young on the cylinder** in the Biot–Savart form: for `c`-periodic `k` and `f`,
`‖∫_cell k(· − y) f(y) dy‖_{Lᵖ(cell)} ≤ ‖k‖_{L¹(cell)} ‖f‖_{Lᵖ(cell)}`. -/
theorem eLpNorm_cellConv_le' {c : ℝ} (hc : 0 < c) {k : Plane → ℝ} {f : Plane → E}
    (hk : StronglyMeasurable k) (hf : StronglyMeasurable f) (hkp : IsPeriodic c k)
    (hper : IsPeriodic c f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => ∫ y in cell c, k (x - y) • f y) p (cellμ c) ≤
      eLpNorm k 1 (cellμ c) * eLpNorm f p (cellμ c) := by
  have : (fun x => ∫ y in cell c, k (x - y) • f y) = fun x => ∫ y in cell c, k y • f (x - y) :=
    funext fun x => integral_cell_mul_comp_sub hc hkp hper x
  rw [this]
  exact eLpNorm_cellConv_le hc hk hf hper hp hp'

/-- The `L¹`-`L^∞` bound for cell convolutions (far part of `K_split`): if `|k| ≤ A`
everywhere, then `‖∫_cell k(x − y) f(y) dy‖ ≤ A ‖f‖_{L¹(cell)}`. -/
theorem enorm_cellConv_le_sup {c : ℝ} {k : Plane → ℝ} {f : Plane → E} {A : ℝ}
    (hA : ∀ z, |k z| ≤ A) (x : Plane) :
    ‖∫ y in cell c, k (x - y) • f y‖ₑ ≤ ENNReal.ofReal A * ∫⁻ y in cell c, ‖f y‖ₑ := by
  calc ‖∫ y in cell c, k (x - y) • f y‖ₑ ≤ ∫⁻ y in cell c, ‖k (x - y) • f y‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in cell c, ENNReal.ofReal A * ‖f y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [enorm_smul, Real.enorm_eq_ofReal_abs]
        gcongr
        exact hA _
    _ = ENNReal.ofReal A * ∫⁻ y in cell c, ‖f y‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Conv

end UnforcedLeray.Cyl
