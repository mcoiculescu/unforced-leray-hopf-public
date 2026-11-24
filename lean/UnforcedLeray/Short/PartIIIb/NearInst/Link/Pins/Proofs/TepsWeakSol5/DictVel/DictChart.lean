import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_1

/-!
# `DictChart` (task `PartIII-b:C/near/pins/3/5/1/3`)

Source `the November 2 reference manuscript` lines 2666-2668.  At `x = ε y` the
recentred chart point of `(ε y, τ)` is the outer chart point of `y` at phase time `τ`:
`perExt c f (Axi.chart ε⁻¹ τ y) = f (cellPt c (cellChart ε c (toCell P (ε y, τ))))`.

Ingredients: `toCell` shifts `τ` by an integer multiple `n P` of the period (`AddCircle` coset);
`cellQ` shifts by `n c`, which `reduceIoc` absorbs; `reduceIoc c q` and `cellRep c q` agree
after the `cellPt` recentring (both are the representative of `q` in the centred cell, up to
the periodicity `c` of `cellRep`); the remaining coordinates are the identities
`ageS (ε y) = age ε⁻¹ y`, `etaCoord ε (ε y) = trans ε⁻¹ y`, and
`cellQ ε (ε y) τ = phase ε⁻¹ τ y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.B0220 (cellChart ageS etaCoord cellQ reduceIoc radius)
open UnforcedLeray.B0223 (PSpace toCell)

/-- `cellRep c` is invariant under integer multiples of `c`. -/
theorem dc_cellRep_int (c : ℝ) (hc : 0 < c) (ξ : ℝ) (n : ℤ) :
    UnforcedLeray.Axi.cellRep c (ξ + n * c) = UnforcedLeray.Axi.cellRep c ξ := by
  have hc0 : c ≠ 0 := hc.ne'
  unfold UnforcedLeray.Axi.cellRep
  have h : (ξ + n * c + c / 2) / c = (ξ + c / 2) / c + n := by
    field_simp <;> ring
  rw [h, Int.floor_add_intCast]
  push_cast
  ring

/-- `reduceIoc c` is invariant under integer multiples of `c`. -/
theorem dc_reduceIoc_int (c : ℝ) (hc : 0 < c) (q : ℝ) (n : ℤ) :
    reduceIoc c (q + n * c) = reduceIoc c q := by
  have hc0 : c ≠ 0 := hc.ne'
  unfold reduceIoc
  have h : (q + n * c) / c = q / c + n := by
    field_simp <;> ring
  rw [h, Int.ceil_add_intCast]
  push_cast
  ring

/-- `reduceIoc c q` lies in the cell `(0, c]`. -/
theorem dc_reduceIoc_mem (c : ℝ) (hc : 0 < c) (q : ℝ) :
    0 < reduceIoc c q ∧ reduceIoc c q ≤ c := by
  unfold reduceIoc
  have h1 : q / c ≤ (⌈q / c⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈q / c⌉ : ℝ) < q / c + 1 := Int.ceil_lt_add_one _
  have e : q / c * c = q := div_mul_cancel₀ q hc.ne'
  have a1 : q ≤ (⌈q / c⌉ : ℝ) * c := by nlinarith
  have a2 : (⌈q / c⌉ : ℝ) * c < q + c := by nlinarith
  constructor <;> nlinarith

/-- The recentred cell representative `if ρ < c/2 then ρ else ρ - c` of `ρ = reduceIoc c ξ`
is `cellRep c ξ`. -/
theorem dc_cellRep_reduce (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    (if reduceIoc c ξ < c / 2 then reduceIoc c ξ else reduceIoc c ξ - c) =
      UnforcedLeray.Axi.cellRep c ξ := by
  have hm := dc_reduceIoc_mem c hc ξ
  have hshift : UnforcedLeray.Axi.cellRep c (reduceIoc c ξ) =
      UnforcedLeray.Axi.cellRep c ξ := by
    have key := dc_cellRep_int c hc ξ (1 - ⌈ξ / c⌉)
    unfold reduceIoc
    rw [← key]
    congr 1
    push_cast
    ring
  rw [← hshift]
  split_ifs with h
  · exact (UnforcedLeray.Axi.cellRep_of_mem hc ⟨by linarith [hm.1], h⟩).symm
  · have hA : UnforcedLeray.Axi.cellRep c (reduceIoc c ξ - c) = reduceIoc c ξ - c :=
      UnforcedLeray.Axi.cellRep_of_mem hc ⟨by linarith [not_lt.1 h], by linarith [hm.2]⟩
    have hB := UnforcedLeray.Axi.cellRep_add hc.ne' (reduceIoc c ξ - c)
    rw [sub_add_cancel] at hB
    rw [hB, hA]

/-- The physical point `(x, τ)` of the periodic space lies in the same class as
`(x, τ + n P)` in the cell `(0, P]`, for some integer `n`. -/
theorem dc_toCell (P : ℝ) [Fact (0 < P)] (x : Space) (τ : ℝ) :
    ∃ n : ℤ, toCell P ((x, (τ : AddCircle P)) : PSpace P) = (x, τ + n * P) := by
  set t : ℝ := ((AddCircle.measurableEquivIoc P 0 (τ : AddCircle P) :
    Ioc (0 : ℝ) (0 + P)) : ℝ) with ht_def
  have h1 : (t : AddCircle P) = (τ : AddCircle P) := AddCircle.coe_equivIoc
  have h2 : ((t - τ : ℝ) : AddCircle P) = 0 := by
    rw [AddCircle.coe_sub, h1, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).1 h2
  have ht : t = τ + n * P := by
    rw [zsmul_eq_mul] at hn
    linarith
  refine ⟨n, ?_⟩
  unfold toCell
  rw [← ht]

/-- The (dilated) cellQ at phase `τ` equals the outer phase `Axi.phase ε⁻¹ τ y`. -/
theorem dc_phase_eq (ε : ℝ) (hε : 0 < ε) (τ : ℝ) (y : Space)
    (hy : y ∉ UnforcedLeray.Axi.axis) :
    UnforcedLeray.Axi.phase ε⁻¹ τ y = cellQ ε (ε • y) τ := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hϱ : 0 < UnforcedLeray.Axi.ϱ y := UnforcedLeray.Axi.ϱ_pos hy
  have hrad : radius (ε • y) = ε * UnforcedLeray.Axi.ϱ y := by
    have h1 : radius (ε • y) = UnforcedLeray.Axi.ϱ (ε • y) := rfl
    rw [h1, UnforcedLeray.Axi.ϱ_smul, abs_of_pos hε]
  unfold UnforcedLeray.Axi.phase UnforcedLeray.Axi.age cellQ
  rw [hrad, Real.log_div (pow_ne_zero 2 (inv_ne_zero hε0)) (pow_ne_zero 2 hϱ.ne'),
    Real.log_pow, Real.log_pow, Real.log_inv, Real.log_mul hε0 hϱ.ne']
  push_cast
  ring

theorem dictChart : DictChart := by
  intro ε c P _ hε hc hP f y hy τ
  have hε0 : ε ≠ 0 := hε.ne'
  have hϱ : 0 < UnforcedLeray.Axi.ϱ y := UnforcedLeray.Axi.ϱ_pos hy
  have hrad : radius (ε • y) = ε * UnforcedLeray.Axi.ϱ y := by
    have h1 : radius (ε • y) = UnforcedLeray.Axi.ϱ (ε • y) := rfl
    rw [h1, UnforcedLeray.Axi.ϱ_smul, abs_of_pos hε]
  obtain ⟨n, hn⟩ := dc_toCell P (ε • y) τ
  have hq_shift : cellQ ε (ε • y) (τ + n * P) = cellQ ε (ε • y) τ + n * c := by
    have hε0' : ε ≠ 0 := hε0
    unfold cellQ
    rw [hP]
    field_simp
    ring
  have hcell : cellChart ε c (ε • y, τ + n * P) =
      (ageS (ε • y), reduceIoc c (cellQ ε (ε • y) τ), etaCoord ε (ε • y)) := by
    dsimp only [cellChart]
    rw [hq_shift, dc_reduceIoc_int c hc _ n]
  rw [hn, hcell]
  dsimp only [UnforcedLeray.Axi.perExt, UnforcedLeray.Axi.chart, cellPt]
  rw [dc_phase_eq ε hε τ y hy, dc_cellRep_reduce c hc]
  congr 1
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · unfold UnforcedLeray.Axi.age ageS
    rw [hrad]
    ring
  · unfold UnforcedLeray.Axi.trans etaCoord
    rw [hrad]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp <;> ring

end UnforcedLeray.Short.PartIIIb.NearInst
