import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.RePartEvenRep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1
import UnforcedLeray.Short.PartIIIa.T20_CTEmbeddings
import UnforcedLeray.Short.PartIIIa.T20_7_BiotSavartExistsUniform
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4

/-!
# `TFKKcEmbed` from the dilation lemmas, through the even representative of the real part

Source of record: `the November 2 reference manuscript`, lines 3176-3184 (the
centrally even zero-circulation class of `eq:ct-embeddings`) and 3228-3240 (`eq:ct-embeddings`,
uniform in `d ≥ 1`, applied at `d = c/√a`).

`eq:ct-embeddings` (`IIIa.CTEmbeddings`) needs a pointwise centrally even datum. The real part
`Re (xFn ξ)` is even only a.e. on the cell (`xFn ξ` is an `L²` representative), so the embedding is
applied to `J_a⁻¹ g` for the even representative `g = reSym ξ` (`rePart_evenRep_zeroCirc`), and
`MemLp`, the weighted norm and the Biot-Savart relation are transported along `g = Re (xFn ξ)` a.e.

The five dilation/bridge facts are the targets of the sibling tasks
`PartIII-b:C/asrc/kflat/1/2/3/1/1/{1,2,3,5,6}`; `tfkKcEmbed_of` assembles them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- Dilation of a Biot-Savart pair (source 3228-3240): if `u = K_c f`, then
`a^{3/2} u(√a ·) = K_{c/√a} (J_a⁻¹ f)`. Target of task `.../1/1/1` (`isBiotSavart_jscaleInv`). -/
def KcBSScale : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ (f : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ),
    IIIa.IsBiotSavart c f u → IIIa.IsBiotSavart (IIIa.cellLen c a) (IIIa.JscaleInv a f)
      (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) j)

/-- Scaling of the velocity norm (source 3228-3240): `‖a^{3/2} u(√a ·)‖_{L²(cell (c/√a))} =
a ‖u‖_{L²(cell c)}`. Target of task `.../1/1/2` (`velNorm_scale`). -/
def KcVelScale : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ u : ℝ × ℝ → Fin 2 → ℂ,
    IIIa.velNorm (IIIa.cellLen c a)
        (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) =
      ENNReal.ofReal a * IIIa.velNorm c u

/-- `‖K_c ξ‖₂ ≤ ‖u‖₂` for any Biot-Savart velocity `u` of `Re ξ` (source 3176-3184, 3228-3240;
`K_c` acts on the real vorticity). Target of task `.../1/1/3` (`kcLp_norm_le_velNorm`). -/
def KcRealBridge : Prop :=
  ∀ {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) (u : ℝ × ℝ → Fin 2 → ℂ),
    IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) u →
      ENNReal.ofReal ‖kcLp ξ‖ ≤ IIIa.velNorm c u

/-- `J_a⁻¹` preserves central evenness and zero circulation, `cell c → cell (c/√a)` (source
3176-3184, 3228-3240). Target of task `.../1/1/5` (`jscaleInv_even_zeroCirc`). -/
def KcJscalePres : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ g : ℝ × ℝ → ℂ, IIIa.IsCentrallyEven g →
    IIIa.HasZeroCirculation c g →
      IIIa.IsCentrallyEven (IIIa.JscaleInv a g) ∧
        IIIa.HasZeroCirculation (IIIa.cellLen c a) (IIIa.JscaleInv a g)

/-- `J_a⁻¹ Re ξ ∈ X_{m,c/√a}` with `‖J_a⁻¹ Re ξ‖ ≤ ‖J_a⁻¹ ξ‖` (source 3228-3240). Target of task
`.../1/1/6` (`jscaleInv_rePart_memLp_le`). -/
def KcMemLpCmp : Prop :=
  ∀ {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (a : ℝ), 1 ≤ a → ∀ ξ : Xmc c m,
    MemLp (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) 2
        (B0579.cellMeasure (IIIa.cellLen c a) m) ∧
      IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) ≤
        IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ))

/-- The Biot-Savart relation only sees the vorticity through cell integrals. -/
theorem isBiotSavart_congr_ae {c : ℝ} {f f' : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (h : IIIa.IsBiotSavart c f u) (hff : f =ᵐ[volume.restrict (B0579.cell c)] f') :
    IIIa.IsBiotSavart c f' u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun ψ hψ => ?_⟩
  rw [← h3 ψ hψ]
  refine integral_congr_ae ?_
  filter_upwards [hff] with x hx
  rw [hx]

/-- a.e. equality on `cell c` gives a.e. equality of `J_a⁻¹` for the weighted measure on
`cell (c/√a)`. -/
theorem jscaleInv_ae_cellMeasure (c a m : ℝ) (ha : 0 < a) {f f' : ℝ × ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] f') :
    IIIa.JscaleInv a f =ᵐ[B0579.cellMeasure (IIIa.cellLen c a) m] IIIa.JscaleInv a f' :=
  ae_cellMeasure_of_ae_cell (IIIa.jscale_ae_of_ae c a ha f f' h)

/-- `1 ≤ c/√a` for `c = ν⁻²`, `0 < ν ≤ 1`, `1 ≤ a ≤ ν⁻¹` (the cells of the short range have
length `≥ 1`, as `eq:ct-embeddings` requires). -/
theorem one_le_cellLen_short {ν c a : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : c = ν ^ (-2 : ℝ))
    (ha1 : 1 ≤ a) (haν : a ≤ ν⁻¹) : 1 ≤ IIIa.cellLen c a := by
  have hνc : ν⁻¹ ≤ c := by
    rw [hc, Real.rpow_neg hν.le, Real.rpow_two]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hν1' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hc1 : 1 ≤ c := hν1'.trans hνc
  have ha0 : 0 < a := one_pos.trans_le ha1
  unfold IIIa.cellLen
  rw [one_le_div (Real.sqrt_pos.2 ha0), Real.sqrt_le_left (zero_le_one.trans hc1)]
  have hcc : c ≤ c ^ 2 := by nlinarith
  linarith

/-- **`TFKKcEmbed`** from the five dilation/bridge facts (source 3176-3184, 3228-3240): apply
`eq:ct-embeddings` at `d = c/√a ≥ 1` to `J_a⁻¹ g`, `g` the even representative of `Re ξ`, with
the velocity `a^{3/2} u(√a ·)` for a Biot-Savart velocity `u` of `g` on `cell c`. -/
theorem tfkKcEmbed_of (m : ℝ) [Fact (1 < m)] (hBS : KcBSScale) (hVel : KcVelScale)
    (hKc : KcRealBridge) (hJ : KcJscalePres) (hM : KcMemLpCmp) : TFKKcEmbed m := by
  intro h8 ν hν hν1 c hc _
  obtain ⟨C1, hC1⟩ := IIIa.ctEmbeddings m h8
  obtain ⟨C2, hC2⟩ := IIIa.CTE.biotSavart_exists_uniform m h8
  have hc0 : 0 < c := Fact.out
  have hc1 : 1 ≤ c := by
    have := one_le_cellLen_short hν hν1 hc le_rfl ((one_le_inv₀ hν).2 hν1)
    simpa [IIIa.cellLen] using this
  refine ⟨max C1 0, le_max_right _ _, fun a ha1 haν ξ => ?_⟩
  have ha0 : 0 < a := one_pos.trans_le ha1
  have hd1 : 1 ≤ IIIa.cellLen c a := one_le_cellLen_short hν hν1 hc ha1 haν
  obtain ⟨g, hg1, hg2, hge, hgz⟩ := rePart_evenRep_zeroCirc ξ
  have hrM : MemLp (fun x => (((xFn ξ x).re : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    (xFn_memLp ξ).re.ofReal
  have hgM : MemLp g 2 (B0579.cellMeasure c m) := hrM.ae_eq hg2.symm
  obtain ⟨u, hu, -⟩ := hC2 c hc1 g hgM hgz hge
  have hur : IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) u :=
    isBiotSavart_congr_ae hu hg1
  have hu' := hBS c a hc0 ha0 g u hu
  obtain ⟨hGe, hGz⟩ := hJ c a hc0 ha0 g hge hgz
  obtain ⟨hMr, hNr⟩ := hM a ha1 ξ
  have hGr := jscaleInv_ae_cellMeasure c a m ha0 hg1
  have hGM : MemLp (IIIa.JscaleInv a g) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) :=
    hMr.ae_eq hGr.symm
  have hEmb := hC1 _ hd1 _ hGM hGz hGe _ hu'
  have hxn : IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a g) =
      IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) :=
    eLpNorm_congr_ae hGr
  have hvel := hVel c a hc0 ha0 u
  have hk := hKc ξ u hur
  calc ENNReal.ofReal ‖kcLp ξ‖ ≤ IIIa.velNorm c u := hk
    _ ≤ ENNReal.ofReal a * IIIa.velNorm c u :=
        le_mul_of_one_le_left' (ENNReal.one_le_ofReal.2 ha1)
    _ = IIIa.velNorm (IIIa.cellLen c a)
          (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
            u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := hvel.symm
    _ ≤ ENNReal.ofReal ‖IIIa.quadQ (IIIa.cellLen c a) (IIIa.JscaleInv a g)‖ +
          IIIa.velNorm (IIIa.cellLen c a)
            (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
              u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := le_add_self
    _ ≤ ENNReal.ofReal C1 * IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a g) := hEmb
    _ ≤ ENNReal.ofReal (max C1 0) * IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a g) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
    _ = ENNReal.ofReal (max C1 0) * IIIa.xNorm (IIIa.cellLen c a) m
          (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) := by rw [hxn]
    _ ≤ ENNReal.ofReal (max C1 0) * IIIa.xNorm (IIIa.cellLen c a) m
          (IIIa.JscaleInv a (xFn ξ)) := mul_le_mul' le_rfl hNr

end UnforcedLeray.Short.PartIIIb.Concrete
