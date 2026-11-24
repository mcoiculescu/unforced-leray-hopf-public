import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4Org

/-!
# The stream transition `Y` on one output bin: kernel Props over the real objects

Source `the November 2 reference manuscript` 5569-5605, 4161-4186, 4171.

Geometry (checked against `IsOutwardCutoff`, `IsStreamCutoff`): the age `s` is `R²/ϱ²` (radius
`ϱ = R/√s`).  The old source `χ_o T` lives at ages `t ≥ 6/(5ν)` (`χ_o` vanishes for `νt ≤ 6/5`), the
stream cutoff `χ_y(νs)` makes `Y` vanish at output ages `s ≥ 1/ν`.  Hence on an output bin
`(s e^{-h}, s]` with nonzero output, `s e^{-h} < 1/ν`, every source age is
`≥ 6/(5ν) > e^{δ}/ν ≥ e^{δ-h}s` (as `δ < log(12/11)`, `e^{δ} < 12/11 < 6/5`): the radial gap
`D ≍ R/√s` of 5588-5589 is automatic.

Props (each over the concrete objects `wardOps`, `wardY`, `chiOStr`, `thinPart`, `bodyMeasure`,
`binSet`, `ReturnLevel.Scut`):

* `WardYBinMassAt` : (a)+(b)+Minkowski, the order-four kernel `L²` bound `C D^{-5/2}` (5588-5591)
  in the form `‖Y g‖_{L²(bin)} ≤ C ν^{-k} ε^{3/2} s^{5/4} · mass_a(g)`, `mass_a(g) = N₀(a)`;
* `ChiOThinRep` : `χ_o (thinPart T)` has a measurable representative `g` vanishing below `6/(5ν)`;
* `BinNormToAge` : gained bin norm to ungained bin norm (`bodyMeasure = π g⁻² ageμ`);
* `MassGained` : the thin mass bound (5571-5575) for the gained norm, with `sup g = e^{γ/ν}`;
* `WardGainMarginG` : the gain bookkeeping (5601-5605).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The ungained `L²` norm of `F` over the output bin `j`, with the measure `ageμ c (-3/2)`. -/
def ageNormBin (c S h : ℝ) (j : ℕ) (F : Chart → Merid) : ℝ≥0∞ :=
  (∫⁻ p in binSet S h j, ‖F p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ)

/-- The thin mass `N₀(a) = ∫_{t>a} ‖g‖ dageμ` (source 5569-5575). -/
def ageMass (c a : ℝ) (g : Chart → Ten3) : ℝ≥0∞ :=
  ∫⁻ p in {p : Chart | a < p.1}, ‖g p‖ₑ ∂(ageμ c (-3 / 2))

/-- **(a)+(b)+Minkowski: the kernel bound for `Y` on one output bin** (source 5585-5593; `Y = D_{μ+1}𝒞_y
(W_μ - W_{μ+1})`, 4171, with `W_μ` the `sepW` integral of the old source `oldPhys`).  For a
source representative `g` supported at ages `≥ 6/(5ν)` and the output bin `j` (upper age `s`), all
source ages exceed `e^{δ-h}s` (radial gap `D ≍ R/√s`); the order-four kernel
(`|D^j∇K| ≤ C|x|^{-4-j}`, `IIIa.SepKernelBounds`, 3604-3610) has spatial `L²` norm `C D^{-5/2}`
(`= C ε^{5/2}s^{5/4}` in the chart normalization), and Minkowski gives
`‖Y g‖_{L²(bin)} ≤ C ν^{-k} ε^{3/2} s^{5/4} N₀(e^{δ-h}s)` (the further `ε^{-1}` is the
normalization of `coefOf`/`oldPhys`). -/
def WardYBinMassAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) (C : ℝ)
    (k : ℕ) : Prop :=
  K.δ < Real.log (12 / 11) → ∀ (j : ℕ) (g : Chart → Ten3), Measurable g →
    (∀ p : Chart, p.1 < 6 / (5 * L.ν) → g p = 0) →
      ageNormBin (cOf L.ν) (L.Scut K) K.hbin j
          (coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g)) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) *
            binUpper (L.Scut K) K.hbin j ^ (5 / 4 : ℝ)) *
          ageMass (cOf L.ν) (Real.exp (K.δ - K.hbin) * binUpper (L.Scut K) K.hbin j) g

/-- Sequence-level `WardYBinMassAt`: constants uniform for large `n` and `z ∈ [-1,1]`. -/
def SeqData.WardYBinMassSeq (D : SeqData) (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    WardYBinMassAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- **The old source of a thin stress** (source 4163-4166, 4171): `χ_o(thinPart T)` has components
`(χ_o T₁, 0)`; the first has a measurable representative `g` vanishing for ages `s ≤ 6/(5ν)`
(`IsOutwardCutoff.zero`), dominated by `|T₁|` (`χ_o ∈ [0,1]`); the second vanishes. -/
def ChiOThinRep : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ), 0 < ν →
    ∀ T : StrG c mZ ρb γ ν, ∃ g : Chart → Ten3, Measurable g ∧
      (∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) ∧
      ((chiOStr c mZ ρb γ ν hχ (thinPart T)).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g ∧
      ((chiOStr c mZ ρb γ ν hχ (thinPart T)).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
        (0 : Chart → Ten3) ∧
      ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ‖g p‖ₑ ≤ ‖(T.fst : Chart → Ten3) p‖ₑ

/-- **Gained bin norm to ungained bin norm** (`bodyMeasure = π g⁻² ageμ(-3/2)`, source 5143): if the
gain `g⁻¹ ≤ G` on the bin, the gained bin norm of `φ ∈ VelG` is at most `√π G` times the ungained
bin `L²` norm of any representative of `φ`. -/
def BinNormToAge : Prop :=
  ∀ (c γ ν S h : ℝ) (j : ℕ) (φ : VelG c γ ν) (F : Chart → Merid) (G : ℝ),
    (φ : Chart → Merid) =ᵐ[bodyMeasure c γ ν] F → 0 ≤ G →
    (∀ p ∈ binSet S h j, ginv γ ν p ≤ G) →
      ENNReal.ofReal (binNorm c γ ν S h j φ) ≤
        ENNReal.ofReal (Real.sqrt Real.pi * G) * ageNormBin c S h j F

/-- **The thin mass bound for the gained norm** (source 5571-5584, 5601): from `ThinMassBound`, for
`T ∈ StrG` and any `g` dominated by `|T₁|`, `N₀(a)(g) ≤ C c^k (a^{-3/4}+a^{-1/2}) e^{γ/ν}‖T‖`
(`‖T₁‖_{Z₁} ≤ sup_{t≥0} g(t) · ‖g⁻¹T₁‖_{Z₁}` and `g(t) = e^{γt/(1+νt)} ≤ e^{γ/ν}`). -/
def MassGained (mZ : ℝ) : Prop :=
  ThinMassBound mZ → ∃ (C0 : ℝ) (k0 : ℕ), ∀ (c ρb γ ν : ℝ), 1 ≤ c → 0 ≤ γ → 0 < ν →
    ∀ (T : StrG c mZ ρb γ ν) (a : ℝ), 0 < a → ∀ g : Chart → Ten3,
      (∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ‖g p‖ₑ ≤ ‖(T.fst : Chart → Ten3) p‖ₑ) →
        ageMass c a g ≤
          ENNReal.ofReal (C0 * c ^ k0 * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ))) *
            Real.exp (γ / ν)) * ‖T‖ₑ

/-- **FALSE for early output bins (`not_wardGainMarginG` in `WardGainMarginFalse.lean`); retired,
replaced by `LateGainMarginG`/`EarlyGainMarginG` there.**  Former gain bookkeeping (source 5601-5605, `ε = e^{-d₀/ν}P_ν`, `d₀ = γ/3`): the kernel factor
`ε^{3/2}`, the source gain `sup_t g(t) = e^{γ/ν}`, and the inverse output gain at the bin's lower age
`s_{j+1}`: `ε^{3/2} e^{γ/ν} ≤ C ν^{-k} e^{γ/(10ν)} g(s_{j+1})`.  (Late outputs `νs ≥ 4/5`:
`3d₀/2 - γ + 4γ/9 = -γ/18`; early sources: `3d₀/2 - 3γ/5 = -γ/10`.) -/
def SeqData.WardGainMarginG (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
    (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν) ≤
      C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
        UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
          (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1))

/-- Arithmetic of the bin: `s^{5/4}(a^{-3/4}+a^{-1/2}) ≤ s^{1/2}+s^{3/4}` for `0 < s ≤ a`. -/
theorem wardBin_arith {s a : ℝ} (hs : 0 < s) (ha : s ≤ a) :
    s ^ (5 / 4 : ℝ) * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ))) ≤
      s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ) := by
  have h1 : a ^ (-(3 / 4 : ℝ)) ≤ s ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs ha (by norm_num)
  have h2 : a ^ (-(1 / 2 : ℝ)) ≤ s ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs ha (by norm_num)
  have e1 : s ^ (5 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) = s ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hs]; norm_num
  have e2 : s ^ (5 / 4 : ℝ) * s ^ (-(1 / 2 : ℝ)) = s ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hs]; norm_num
  have hp : 0 ≤ s ^ (5 / 4 : ℝ) := Real.rpow_nonneg hs.le _
  calc s ^ (5 / 4 : ℝ) * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ)))
      ≤ s ^ (5 / 4 : ℝ) * (s ^ (-(3 / 4 : ℝ)) + s ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hp
    _ = s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ) := by rw [mul_add, e1, e2]

/-- The gain is monotone in the age (for `γ ≥ 0`, `ν > 0`). -/
theorem gainG_mono {γ ν s s' : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 0 ≤ s) (hss : s ≤ s') :
    UnforcedLeray.Short.IIIa.gainG γ ν s ≤ UnforcedLeray.Short.IIIa.gainG γ ν s' := by
  unfold UnforcedLeray.Short.IIIa.gainG
  refine Real.exp_le_exp.2 ?_
  have h1 : 0 < 1 + ν * s := by nlinarith
  have h2 : 0 < 1 + ν * s' := by nlinarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 hss)]

end UnforcedLeray.Short.PartIIIb.Concrete

end
