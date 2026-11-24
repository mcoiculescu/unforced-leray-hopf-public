import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphFlat
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows
import UnforcedLeray.Short.PartIIb.Tasks.HardyL1

/-!
# Part II-b, task `PartII-b:F5`: the body source bound `short-bg:source` (conditional)

Source of record: `the November 2 reference manuscript` (SP), lines 2211-2246,
display `short-bg:source` at line 2237:

  "Let `F ∈ H_p`, set `b_0 = T_0 F`, and solve the meridional correction
  `z_s - νΔz + P_0(v·∇z + z·∇v) = g := -P_0(v·∇b_0 + b_0·∇v)`. ...
  The global free graph gives `‖b_0‖_{H_p} + ‖√(νs) Db_0‖_{H_p} + ‖νs D²b_0‖_{H_p} ≤ C ‖F‖_{H_p}`.
  Put `b = 13/8`, so `b - p = -9/8`. Spatial Hölder with `22/3`, followed by one derivative,
  bounds both `g` in `H¹` and `curl g` in `X_m` on a finite slow-age band by
  `𝒫_ν(‖D²b_0‖_p + ‖Db_0‖_p + ‖b_0‖_p)`. Thus
  `‖g‖_{L^p((0,T), s^b ds; H¹)} + ‖curl g‖_{L^p((0,T), s^b ds; X_m)} ≤ 𝒫_ν ‖F‖_{H_p}`.
  The circulation of the curl source is zero."

## Statements and concrete definitions

* `flatBv tr b gq gη`: the unprojected convective interaction `v·∇_{q,η} b + b·∇_{q,η} v`
  (related to `flatK` of `StatementsFree.lean` by `flatK = s • flatBv`, proved in
  `flatK_eq_smul_flatBv`);
* `IsBodySource tr b0 b0q b0η g`: the planar solenoidal-test characterization of
  `g = -P_0(v·∇b_0 + b_0·∇v)` (following the pattern of `IsFlatResponse` in `Defs.lean`);
* `profCurl gq gη`: the scalar curl `∂_q g_z - ∂_η g_r` of a profile with weak first derivatives
  `gq = ∂_q g`, `gη = ∂_η g`;
* `sliceLpNorm`, `sliceH1Norm`, `sliceXmNorm`, and `sLpNorm`: the slice norms on the cylinder cell
  and the `L^p((0, T), s^b ds)` Bochner-norm functional matching `HardyL1` / `HardySingular` in
  `StatementsMixed.lean`;
* `BodySourceBound`: the target statement `short-bg:source` (SP 2237-2239).

## Proved here (zero `sorry`)

* `flatK_eq_smul_flatBv`: `flatK tr b gq gη x = (x.1 : ℂ) • flatBv tr b gq gη x`;
* `profileGraphFlat_bgp` and `flat_graph_bound_bgp`: specialization of `ProfileGraphFlat`
  (`PartII-b:T14`, `profileGraphFlat_proof`) and `flat_graph_bound` (`PartII-b:T13`) to the
  background exponent `p = bgp = 11/4` and shift `μ = 0` (`gap = 1/22 > 0`);
* `sLpNorm_D2_eq`, `sLpNorm_D1_le`, `sLpNorm_D0_le`: the exact age-weight conversion on `(0, T]`
  between the `H_p` age measure `s^{-9/8} ds` and `s^{13/8} ds` (`b = 13/8`, `b - p = -9/8`,
  SP 2228) for `D²b_0`, `Db_0`, and `b_0`;
* `bodySourceBound_of`: conditional assembly of `BodySourceBound` from `FlatGraphD2Slice`
  (`PartII-b:F5/1`, the slice-level second-order free graph bound from `T14`) and
  `BodySourceSliceHolder` (`PartII-b:F5/2`, the spatial `L^{22/3}` Hölder + one-derivative estimate
  and zero circulation of the curl source on `[0, Σ/ν]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## The unprojected convective interaction and `IsBodySource` -/

/-- Multiplication of a profile by the age coordinate `s = x.1`. -/
def mulS (b : CProf) : CProf := fun x => (x.1 : ℂ) • b x

/-- The unprojected convective interaction `B_v b = (v·∇_{q,η}) b + (b·∇_{q,η}) v` of the flat train
`v = v_c(s)` with a profile `b` having weak spatial derivatives `gq = ∂_q b`, `gη = ∂_η b`
(SP 2216, 2314). -/
def flatBv {ν c : ℝ} (tr : B0140.TrainSol ν c) (b gq gη : CProf) (x : Coord) : CMerid :=
  WithLp.toLp 2 fun i : Fin 2 =>
    ((tr.v x.1 x.2 0 : ℝ) : ℂ) * gq x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * gη x i +
      b x 0 * ((fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ) +
      b x 1 * ((fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ)

/-- `flatK = s B_v`: the flat interaction `flatK` of `StatementsFree.lean` is `mulS (flatBv ...)`. -/
theorem flatK_eq_smul_flatBv {ν c : ℝ} (tr : B0140.TrainSol ν c) (b gq gη : CProf) (x : Coord) :
    flatK tr b gq gη x = (x.1 : ℂ) • flatBv tr b gq gη x := by
  ext i
  simp [flatK, flatBv]
  ring

/-- `g = -P_0(v·∇b_0 + b_0·∇v)` in `(0, ∞) × ℝ²` (SP 2216), characterized via `IsPlanarSolTest`
pairing following `IsFlatResponse` in `Defs.lean`: `g` is weakly solenoidal in `(q, η)` on `s > 0`,
and for every planar solenoidal test `Ψ` (`IsPlanarSolTest Ψ`, on which `P_0` is invisible),
`∫ g · Ψ = -∫ (v·∇b_0 + b_0·∇v) · Ψ`. -/
structure IsBodySource {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0 b0q b0η g : CProf) : Prop where
  solenoidal : ∀ φ, IsCoordTest φ →
    Integrable (fun x => g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) = 0
  equation : ∀ Ψ, IsPlanarSolTest Ψ →
    Integrable (cdot g Ψ) ∧
      Integrable (cdot (flatBv tr b0 b0q b0η) Ψ) ∧
      ∫ x, cdot g Ψ x = -∫ x, cdot (flatBv tr b0 b0q b0η) Ψ x

/-- The weak scalar curl `∂_q g_z - ∂_η g_r` of a profile `g` with weak spatial derivatives
`gq = ∂_q g`, `gη = ∂_η g` (matching `Cyl.curl` in `Lib/Cylinder/Basic.lean`). -/
def profCurl (gq gη : CProf) (x : Coord) : ℂ := gq x 1 - gη x 0

/-! ## Slice norms and the `L^p((0, T), s^b ds)` Bochner norm -/

/-- The spatial `L^p(dq/c dη)` slice norm (`p = bgp = 11/4`) of a profile `u` at age `s`. -/
def sliceLpNorm (c : ℝ) (u : CProf) (s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun z => u (s, z)) (ENNReal.ofReal bgp) (UnforcedLeray.Cyl.avgμ c)

/-- The cylinder `H¹(C_c)` slice norm of a profile `g` with weak spatial derivatives `gq = ∂_q g`,
`gη = ∂_η g` at age `s`: `‖g(s)‖_{L²(cell)} + ‖∂_q g(s)‖_{L²(cell)} + ‖∂_η g(s)‖_{L²(cell)}`. -/
def sliceH1Norm (c : ℝ) (g gq gη : CProf) (s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
    eLpNorm (fun z => gq (s, z)) 2 (volume.restrict (B0579.cell c)) +
    eLpNorm (fun z => gη (s, z)) 2 (volume.restrict (B0579.cell c))

/-- The weighted `X_{m,c} = L²(C_c, (1+q²+η²)^m)` slice norm of a scalar vorticity field `w` at
age `s`. -/
def sliceXmNorm (c m : ℝ) (w : Coord → ℂ) (s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun z => w (s, z)) 2 (B0579.cellMeasure c m)

/-- The `L^p((0, T), s^b ds)` norm (`p = bgp = 11/4`, `1/p = 4/11`) of a nonnegative slice norm
`N : ℝ → ℝ≥0∞`, matching `HardyL1` and `HardySingular` in `StatementsMixed.lean`. -/
def sLpNorm (b T : ℝ) (N : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ s in Ioc 0 T, N s ^ bgp ∂sMeas b) ^ (4 / 11 : ℝ)

/-! ## Target statement and leaf propositions -/

/-- **Target of `PartII-b:F5`** (`short-bg:source`, SP 2234-2239): for every `m > 8`, slow age
`Σ > 0` (`T = Σ/ν`), and regime bounds `0 < d₋ ≤ d₊`, there are `C > 0`, `k : ℕ`, `ν₀ > 0` such
that at every parameter point of `BgRegime` with `ν ≤ ν₀`, for every body force `F ∈ H_p` and its
flat response `b_0 = T_0 F`, there exist `b_0`'s weak spatial derivatives `b0q = ∂_q b_0`,
`b0η = ∂_η b_0` and the projected source `g = -P_0(v·∇b_0 + b_0·∇v)` with weak spatial derivatives
`gq = ∂_q g`, `gη = ∂_η g` such that:
1. `g` is `c`-periodic in `q` and satisfies `IsBodySource p.train b0 b0q b0η g`;
2. the slice norms `s ↦ ‖g(s)‖_{H¹}` and `s ↦ ‖curl g(s)‖_{X_m}` are measurable and satisfy
   `‖g‖_{L^p((0,T),s^{13/8}ds;H¹)} + ‖curl g‖_{L^p((0,T),s^{13/8}ds;X_m)} ≤ C ν^{-k} ‖F‖_{H_p}`;
3. the circulation of `curl g` on the cell vanishes for a.e. `s ∈ (0, T]`. -/
def BodySourceBound : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ F b0 : CProf, InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
        ∃ b0q b0η g gq gη : CProf,
          HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
          QPeriodic p.c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
          IsBodySource p.train b0 b0q b0η g ∧
          Measurable (sliceH1Norm p.c g gq gη) ∧
          Measurable (sliceXmNorm p.c m (profCurl gq gη)) ∧
          sLpNorm (13 / 8) (Sig / p.ν) (sliceH1Norm p.c g gq gη) +
              sLpNorm (13 / 8) (Sig / p.ν) (sliceXmNorm p.c m (profCurl gq gη)) ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹) * hNorm p.c bgp F ∧
          (∀ᵐ s ∂volume, s ∈ Ioc 0 (Sig / p.ν) →
            IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
              ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0)

/-- **Leaf 1 (`PartII-b:F5/1`)**: the slice-level global free graph bound up to second spatial
derivatives (SP 2224-2227: `‖b_0‖_{H_p} + ‖√(νs) Db_0‖_{H_p} + ‖νs D²b_0‖_{H_p} ≤ C ‖F‖_{H_p}`).
From `ProfileGraphFlat` (`PartII-b:T14`) and the dyadic-window cylinder heat estimate
(`CylHeatMaxReg`, `WeakGlue`, `DyadicSummation` in `Tasks/FlatWindows`), every flat response `b0`
in the flat class has a strongly measurable periodic representative `b0'` (agreeing with `b0`
Lebesgue-a.e. on `s > 0`), weak first derivatives `b0q, b0η`, and weak second spatial derivatives
`D2 : Fin 2 → Fin 2 → CProf` (all strongly measurable and in `H_p` with the appropriate age
weights `1`, `√s`, `s`) whose slice `L^p(Cyl.avgμ c)` norms are measurable and bounded in
`sMeas (-9 / 8)` on `(0, T]` by `C ‖F‖_{H_p}`. -/
def FlatGraphD2Slice : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ν c T : ℝ, 0 < ν → 0 < c → 0 < T →
    ∀ F b0 : CProf, InHr c bgp F → InFlatClass c bgp b0 → IsFlatResponse ν 0 F b0 →
      ∃ (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
        (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) ∧
        InHr c bgp b0' ∧ InHr c bgp (sqrtS b0q) ∧ InHr c bgp (sqrtS b0η) ∧
        (∀ i j, InHr c bgp (mulS (D2 i j))) ∧
        StronglyMeasurable b0' ∧ StronglyMeasurable b0q ∧ StronglyMeasurable b0η ∧
        (∀ i j, StronglyMeasurable (D2 i j)) ∧
        HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
        HasWeakVec vQ0 dZero b0q (D2 0 0) ∧ HasWeakVec vEta dZero b0q (D2 0 1) ∧
        HasWeakVec vQ0 dZero b0η (D2 1 0) ∧ HasWeakVec vEta dZero b0η (D2 1 1) ∧
        Measurable (sliceLpNorm c b0') ∧
        Measurable (sliceLpNorm c b0q) ∧
        Measurable (sliceLpNorm c b0η) ∧
        (∀ i j, Measurable (sliceLpNorm c (D2 i j))) ∧
        sLpNorm (-9 / 8) T (sliceLpNorm c b0') ≤ ENNReal.ofReal C * hNorm c bgp F ∧
        ENNReal.ofReal (Real.sqrt ν) *
            sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm c b0q s) ≤
          ENNReal.ofReal C * hNorm c bgp F ∧
        ENNReal.ofReal (Real.sqrt ν) *
            sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm c b0η s) ≤
          ENNReal.ofReal C * hNorm c bgp F ∧
        (∀ i j : Fin 2, ENNReal.ofReal ν *
            sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal s * sliceLpNorm c (D2 i j) s) ≤
          ENNReal.ofReal C * hNorm c bgp F)

/-- **Leaf 2 (`PartII-b:F5/2`)**: spatial Hölder with `22/3` (`1/2 = 3/22 + 4/11`) followed by one
derivative on a finite slow-age band `[0, Σ/ν]`, together with zero circulation of the curl source
(SP 2228-2239, using `short-bg:train-uniform` SP 2052 and the weighted `L^{22/3}` train bounds of
Part I Lemma `sct:heat`). -/
def BodySourceSliceHolder : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ (b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
        InFlatClass p.c bgp b0 →
        (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
        InHr p.c bgp b0' → InHr p.c bgp (sqrtS b0q) → InHr p.c bgp (sqrtS b0η) →
        (∀ i j, InHr p.c bgp (mulS (D2 i j))) →
        StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
        (∀ i j, StronglyMeasurable (D2 i j)) →
        HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
        HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
        HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
        Measurable (sliceLpNorm p.c b0') →
        Measurable (sliceLpNorm p.c b0q) →
        Measurable (sliceLpNorm p.c b0η) →
        (∀ i j, Measurable (sliceLpNorm p.c (D2 i j))) →
        ∃ g gq gη : CProf,
          QPeriodic p.c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
          IsBodySource p.train b0 b0q b0η g ∧
          Measurable (sliceH1Norm p.c g gq gη) ∧
          Measurable (sliceXmNorm p.c m (profCurl gq gη)) ∧
          sLpNorm (13 / 8) (Sig / p.ν) (sliceH1Norm p.c g gq gη) +
              sLpNorm (13 / 8) (Sig / p.ν) (sliceXmNorm p.c m (profCurl gq gη)) ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹) *
              (sLpNorm (13 / 8) (Sig / p.ν) (sliceLpNorm p.c b0') +
                sLpNorm (13 / 8) (Sig / p.ν) (sliceLpNorm p.c b0q) +
                sLpNorm (13 / 8) (Sig / p.ν) (sliceLpNorm p.c b0η) +
                ∑ i : Fin 2, ∑ j : Fin 2,
                  sLpNorm (13 / 8) (Sig / p.ν) (sliceLpNorm p.c (D2 i j))) ∧
          (∀ᵐ s ∂volume, s ∈ Ioc 0 (Sig / p.ν) →
            IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
              ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0)

/-! ## Specialization of `ProfileGraphFlat` (`PartII-b:T14`) to `r = bgp = 11/4`, `μ = 0` -/

theorem bgp_gt_one : 1 < bgp := by norm_num [bgp]

theorem bgp_lt_three : bgp < 3 := by norm_num [bgp]

theorem bgp_gap_pos : 0 < (0 : ℂ).re + (3 / bgp - 1) / 2 := by norm_num [bgp]

/-- Specialization of `profileGraphFlat_proof` (`PartII-b:T14`) to `r = bgp = 11/4` and `μ = 0`. -/
theorem profileGraphFlat_bgp :
    ∃ C : ℝ, 0 < C ∧ ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ F : CProf, InHr c bgp F →
      ∃ b, InFlatClass c bgp b ∧ IsFlatResponse ν 0 F b ∧ GraphBound ν c bgp 0 C F b ∧
        ∀ b', InFlatClass c bgp b' → IsFlatResponse ν 0 F b' → b' =ᵐ[hMeas c bgp] b :=
  profileGraphFlat_proof bgp bgp_gt_one bgp_lt_three 0 bgp_gap_pos

/-- Specialization of `flat_graph_bound` (`PartII-b:T13`) to `r = bgp = 11/4` and `μ = 0` with a
positive constant `C > 0`. -/
theorem flat_graph_bound_bgp :
    ∃ C : ℝ, 0 < C ∧ ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ F b0 : CProf,
      InHr c bgp F → InFlatClass c bgp b0 → IsFlatResponse ν 0 F b0 →
      GraphBound ν c bgp 0 C F b0 := by
  obtain ⟨C, hC⟩ := flat_graph_bound bgp bgp_gt_one bgp_lt_three 0 bgp_gap_pos
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun ν c hν hc F b0 hF hb0 hresp => ?_⟩
  obtain ⟨Sb, Qb, Eb, h1, h2, h3, hn⟩ := hC ν c hν hc F hF b0 hresp hb0
  have hle : ENNReal.ofReal C ≤ ENNReal.ofReal (max C 1) :=
    ENNReal.ofReal_le_ofReal (le_max_left C 1)
  exact ⟨Sb, Qb, Eb, h1, h2, h3, hn.trans (by gcongr)⟩

/-! ## Age-weight conversion between `s^{-9/8} ds` and `s^{13/8} ds` (`b = 13/8`, `b - p = -9/8`) -/

/-- Pointwise identity `(s · x)^{11/4} · s^{-9/8} = x^{11/4} · s^{13/8}` for `s > 0`
(SP 2228: "Put `b = 13/8`, so `b - p = -9/8`"). -/
theorem bodySource_d2_factor (s : ℝ) (hs : 0 < s) (x : ℝ≥0∞) :
    (ENNReal.ofReal s * x) ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)) =
      x ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) := by
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have hexp : bgp + (-9 / 8 : ℝ) = 13 / 8 := by norm_num [bgp]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hbgp, ENNReal.ofReal_rpow_of_nonneg hs.le hbgp,
    mul_comm (ENNReal.ofReal (s ^ bgp)) (x ^ bgp), mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le bgp), ← Real.rpow_add hs, hexp]

/-- Exact equality of the `s^{13/8} ds` norm of `N` and the `s^{-9/8} ds` norm of `s ↦ s · N s` on
`(0, T]` (`b - p = 13/8 - 11/4 = -9/8`, used for `D²b_0`). -/
theorem sLpNorm_D2_eq (T : ℝ) (N : ℝ → ℝ≥0∞) (hN : Measurable N) :
    sLpNorm (13 / 8) T N = sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal s * N s) := by
  unfold sLpNorm
  congr 1
  have hm1 : Measurable (fun s : ℝ => N s ^ bgp) := by fun_prop
  have hm2 : Measurable (fun s : ℝ => (ENNReal.ofReal s * N s) ^ bgp) := by fun_prop
  rw [hardyL1_sMeas_Ioc (13 / 8) T _ hm1, hardyL1_sMeas_Ioc (-9 / 8) T _ hm2]
  refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  exact (bodySource_d2_factor s hs.1 (N s)).symm

/-- On `(0, T]`, the `s^{13/8} ds` norm of `N` is bounded by `√T` times the `s^{-9/8} ds` norm of
`s ↦ √s · N s` (used for `Db_0`). -/
theorem sLpNorm_D1_le (T : ℝ) (N : ℝ → ℝ≥0∞) (hN : Measurable N) :
    sLpNorm (13 / 8) T N ≤
      ENNReal.ofReal (Real.sqrt T) *
        sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * N s) := by
  rw [sLpNorm_D2_eq T N hN]
  unfold sLpNorm
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have h411 : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hmul : bgp * (4 / 11 : ℝ) = 1 := by norm_num [bgp]
  have hpow : ENNReal.ofReal (Real.sqrt T) =
      (ENNReal.ofReal (Real.sqrt T) ^ bgp) ^ (4 / 11 : ℝ) := by
    rw [← ENNReal.rpow_mul, hmul, ENNReal.rpow_one]
  rw [hpow, ← ENNReal.mul_rpow_of_nonneg _ _ h411,
    ← lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hbgp ENNReal.ofReal_ne_top).ne]
  refine ENNReal.rpow_le_rpow ?_ h411
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hbgp]
  refine ENNReal.rpow_le_rpow ?_ hbgp
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg T)]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  calc s = Real.sqrt s * Real.sqrt s := (Real.mul_self_sqrt hs.1.le).symm
    _ ≤ Real.sqrt T * Real.sqrt s :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs.2) (Real.sqrt_nonneg s)

/-- On `(0, T]`, the `s^{13/8} ds` norm of `N` is bounded by `T` times the `s^{-9/8} ds` norm of `N`
(used for `b_0`). -/
theorem sLpNorm_D0_le (T : ℝ) (N : ℝ → ℝ≥0∞) (hN : Measurable N) :
    sLpNorm (13 / 8) T N ≤ ENNReal.ofReal T * sLpNorm (-9 / 8) T N := by
  rw [sLpNorm_D2_eq T N hN]
  unfold sLpNorm
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have h411 : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hmul : bgp * (4 / 11 : ℝ) = 1 := by norm_num [bgp]
  have hpow : ENNReal.ofReal T = (ENNReal.ofReal T ^ bgp) ^ (4 / 11 : ℝ) := by
    rw [← ENNReal.rpow_mul, hmul, ENNReal.rpow_one]
  rw [hpow, ← ENNReal.mul_rpow_of_nonneg _ _ h411,
    ← lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hbgp ENNReal.ofReal_ne_top).ne]
  refine ENNReal.rpow_le_rpow ?_ h411
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hbgp]
  refine ENNReal.rpow_le_rpow ?_ hbgp
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hs.2) zero_le

/-! ## Conditional assembly of `BodySourceBound` -/

/-- Helper: cancellation of `√ν` in `√(Sig/ν) · (√ν)⁻¹ = √Sig · ν⁻¹` for `Sig, ν > 0`. -/
private theorem sqrt_div_mul_inv_sqrt {Sig ν : ℝ} (hSig : 0 < Sig) (hν : 0 < ν) :
    Real.sqrt (Sig / ν) * (Real.sqrt ν)⁻¹ = Real.sqrt Sig * ν⁻¹ := by
  rw [Real.sqrt_div hSig.le, div_eq_mul_inv, mul_assoc, ← mul_inv, Real.mul_self_sqrt hν.le]

/-- **Conditional assembly of `PartII-b:F5`** (`BodySourceBound`, SP 2234-2239) from
`FlatGraphD2Slice` (`PartII-b:F5/1`) and `BodySourceSliceHolder` (`PartII-b:F5/2`), using the proved
age-weight conversions `sLpNorm_D2_eq`, `sLpNorm_D1_le`, `sLpNorm_D0_le`. -/
theorem bodySourceBound_of (hG : FlatGraphD2Slice) (hH : BodySourceSliceHolder) :
    BodySourceBound := by
  intro m hm Sig hSig dm dp hdm
  obtain ⟨C₂, hC₂, hG₂⟩ := hG
  obtain ⟨C₃, k₃, ν₀, hC₃, hν₀, hH₃⟩ := hH m hm Sig hSig dm dp hdm
  set K : ℝ := C₃ * ((Sig + 2 * Real.sqrt Sig + 4) * C₂)
  have hK : 0 < K := by positivity
  refine ⟨K, k₃ + 1, ν₀, hK, hν₀, fun p d hreg hν F b0 hF hb0 hresp => ?_⟩
  have hνp : 0 < p.ν := p.ν_pos
  have hcp : 0 < p.c := by rw [hreg.c_eq]; positivity
  set T : ℝ := Sig / p.ν
  have hTp : 0 < T := div_pos hSig hνp
  obtain ⟨b0', b0q, b0η, D2, hae0, hb0'H, hbqH, hbηH, hD2H,
    hsm0, hsmq, hsmη, hsmD2, hwq, hwη, hw00, hw01, hw10, hw11,
    hm0, hmq, hmη, hmD2, hb0_bd, hbq_bd, hbη_bd, hD2_bd⟩ :=
    hG₂ p.ν p.c T hνp hcp hTp F b0 hF hb0 hresp
  obtain ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc, hmg1, hmgc, hg_bd, hg_circ⟩ :=
    hH₃ p d hreg hν b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 hm0 hmq hmη hmD2
  refine ⟨b0q, b0η, g, gq, gη, hwq, hwη, hgper, hgwq, hgwη, hgsrc, hmg1, hmgc, ?_, hg_circ⟩
  -- 1. Convert the `s^{-9/8}` bounds of `b0'`, `b0q`, `b0η`, `D2 i j` to `s^{13/8}` on `(0, T]`.
  have h0_13 : sLpNorm (13 / 8) T (sliceLpNorm p.c b0') ≤
      ENNReal.ofReal (Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
    calc sLpNorm (13 / 8) T (sliceLpNorm p.c b0')
        ≤ ENNReal.ofReal T * sLpNorm (-9 / 8) T (sliceLpNorm p.c b0') :=
          sLpNorm_D0_le T _ hm0
      _ ≤ ENNReal.ofReal T * (ENNReal.ofReal C₂ * hNorm p.c bgp F) := by gcongr
      _ = ENNReal.ofReal (Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hTp.le]
          congr 2
          dsimp [T]
          ring
  have hsqν_pos : 0 < Real.sqrt p.ν := Real.sqrt_pos.2 hνp
  have hq_9 : sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0q s) ≤
      ENNReal.ofReal ((Real.sqrt p.ν)⁻¹ * C₂) * hNorm p.c bgp F := by
    calc sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0q s)
        = ENNReal.ofReal (Real.sqrt p.ν)⁻¹ *
            (ENNReal.ofReal (Real.sqrt p.ν) *
              sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0q s)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hsqν_pos.le),
            inv_mul_cancel₀ hsqν_pos.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (Real.sqrt p.ν)⁻¹ * (ENNReal.ofReal C₂ * hNorm p.c bgp F) := by gcongr
      _ = ENNReal.ofReal ((Real.sqrt p.ν)⁻¹ * C₂) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hsqν_pos.le)]
  have hq_13 : sLpNorm (13 / 8) T (sliceLpNorm p.c b0q) ≤
      ENNReal.ofReal (Real.sqrt Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
    calc sLpNorm (13 / 8) T (sliceLpNorm p.c b0q)
        ≤ ENNReal.ofReal (Real.sqrt T) *
            sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0q s) :=
          sLpNorm_D1_le T _ hmq
      _ ≤ ENNReal.ofReal (Real.sqrt T) *
            (ENNReal.ofReal ((Real.sqrt p.ν)⁻¹ * C₂) * hNorm p.c bgp F) := by gcongr
      _ = ENNReal.ofReal (Real.sqrt Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg T)]
          congr 2
          calc Real.sqrt T * ((Real.sqrt p.ν)⁻¹ * C₂)
              = (Real.sqrt (Sig / p.ν) * (Real.sqrt p.ν)⁻¹) * C₂ := by dsimp [T]; ring
            _ = Real.sqrt Sig * C₂ * p.ν⁻¹ := by
              rw [sqrt_div_mul_inv_sqrt hSig hνp]; ring
  have hη_9 : sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0η s) ≤
      ENNReal.ofReal ((Real.sqrt p.ν)⁻¹ * C₂) * hNorm p.c bgp F := by
    calc sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0η s)
        = ENNReal.ofReal (Real.sqrt p.ν)⁻¹ *
            (ENNReal.ofReal (Real.sqrt p.ν) *
              sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0η s)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hsqν_pos.le),
            inv_mul_cancel₀ hsqν_pos.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (Real.sqrt p.ν)⁻¹ * (ENNReal.ofReal C₂ * hNorm p.c bgp F) := by gcongr
      _ = ENNReal.ofReal ((Real.sqrt p.ν)⁻¹ * C₂) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hsqν_pos.le)]
  have hη_13 : sLpNorm (13 / 8) T (sliceLpNorm p.c b0η) ≤
      ENNReal.ofReal (Real.sqrt Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
    calc sLpNorm (13 / 8) T (sliceLpNorm p.c b0η)
        ≤ ENNReal.ofReal (Real.sqrt T) *
            sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm p.c b0η s) :=
          sLpNorm_D1_le T _ hmη
      _ ≤ ENNReal.ofReal (Real.sqrt T) *
            (ENNReal.ofReal ((Real.sqrt p.ν)⁻¹ * C₂) * hNorm p.c bgp F) := by gcongr
      _ = ENNReal.ofReal (Real.sqrt Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg T)]
          congr 2
          calc Real.sqrt T * ((Real.sqrt p.ν)⁻¹ * C₂)
              = (Real.sqrt (Sig / p.ν) * (Real.sqrt p.ν)⁻¹) * C₂ := by dsimp [T]; ring
            _ = Real.sqrt Sig * C₂ * p.ν⁻¹ := by
              rw [sqrt_div_mul_inv_sqrt hSig hνp]; ring
  have hD2_13 : ∀ i j : Fin 2, sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 i j)) ≤
      ENNReal.ofReal (C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
    intro i j
    rw [sLpNorm_D2_eq T _ (hmD2 i j)]
    calc sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal s * sliceLpNorm p.c (D2 i j) s)
        = ENNReal.ofReal p.ν⁻¹ *
            (ENNReal.ofReal p.ν *
              sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal s * sliceLpNorm p.c (D2 i j) s)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hνp.le),
            inv_mul_cancel₀ hνp.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal p.ν⁻¹ * (ENNReal.ofReal C₂ * hNorm p.c bgp F) :=
          mul_le_mul_of_nonneg_left (hD2_bd i j) zero_le
      _ = ENNReal.ofReal (C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hνp.le), mul_comm p.ν⁻¹ C₂]
  -- 2. Sum the seven bounds and multiply by `C₃ * (p.ν ^ k₃)⁻¹`.
  have hsum : sLpNorm (13 / 8) T (sliceLpNorm p.c b0') +
        sLpNorm (13 / 8) T (sliceLpNorm p.c b0q) +
        sLpNorm (13 / 8) T (sliceLpNorm p.c b0η) +
        ∑ i : Fin 2, ∑ j : Fin 2, sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 i j)) ≤
      ENNReal.ofReal ((Sig + 2 * Real.sqrt Sig + 4) * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    calc sLpNorm (13 / 8) T (sliceLpNorm p.c b0') +
          sLpNorm (13 / 8) T (sliceLpNorm p.c b0q) +
          sLpNorm (13 / 8) T (sliceLpNorm p.c b0η) +
          (sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 0 0)) +
            sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 0 1)) +
            (sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 1 0)) +
              sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 1 1))))
        ≤ ENNReal.ofReal (Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F +
          ENNReal.ofReal (Real.sqrt Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F +
          ENNReal.ofReal (Real.sqrt Sig * C₂ * p.ν⁻¹) * hNorm p.c bgp F +
          (ENNReal.ofReal (C₂ * p.ν⁻¹) * hNorm p.c bgp F +
            ENNReal.ofReal (C₂ * p.ν⁻¹) * hNorm p.c bgp F +
            (ENNReal.ofReal (C₂ * p.ν⁻¹) * hNorm p.c bgp F +
              ENNReal.ofReal (C₂ * p.ν⁻¹) * hNorm p.c bgp F)) := by
          gcongr
          · exact hD2_13 0 0
          · exact hD2_13 0 1
          · exact hD2_13 1 0
          · exact hD2_13 1 1
      _ = ENNReal.ofReal ((Sig + 2 * Real.sqrt Sig + 4) * C₂ * p.ν⁻¹) * hNorm p.c bgp F := by
          repeat rw [← add_mul]
          congr 1
          repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  calc sLpNorm (13 / 8) T (sliceH1Norm p.c g gq gη) +
        sLpNorm (13 / 8) T (sliceXmNorm p.c m (profCurl gq gη))
      ≤ ENNReal.ofReal (C₃ * (p.ν ^ k₃)⁻¹) *
          (sLpNorm (13 / 8) T (sliceLpNorm p.c b0') +
            sLpNorm (13 / 8) T (sliceLpNorm p.c b0q) +
            sLpNorm (13 / 8) T (sliceLpNorm p.c b0η) +
            ∑ i : Fin 2, ∑ j : Fin 2, sLpNorm (13 / 8) T (sliceLpNorm p.c (D2 i j))) := hg_bd
    _ ≤ ENNReal.ofReal (C₃ * (p.ν ^ k₃)⁻¹) *
          (ENNReal.ofReal ((Sig + 2 * Real.sqrt Sig + 4) * C₂ * p.ν⁻¹) * hNorm p.c bgp F) := by
        gcongr
    _ = ENNReal.ofReal (K * (p.ν ^ (k₃ + 1))⁻¹) * hNorm p.c bgp F := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        dsimp [K]
        rw [pow_succ, mul_inv]
        ring

end UnforcedLeray.Short.IIb

end
