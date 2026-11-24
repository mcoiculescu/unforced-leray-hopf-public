import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Rotations about the vertical axis (source 2666-2668, axisymmetry)

If `hRad y = hRad y'` and `y₂ = y'₂`, the planar rotation with `cos θ = c`, `sin θ = s` where
`(c, s) = (y₀y'₀ + y₁y'₁, y₀y'₁ − y₁y'₀)/(y₀²+y₁²)` carries `y` to `y'`, fixes the vertical
coordinate and preserves `hRad`.  When `y₀²+y₁² = 0` the two points coincide on the axis and the
identity works.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The rotation `(z₀,z₁,z₂) ↦ (c z₀ - s z₁, s z₀ + c z₁, z₂)` about the vertical axis. -/
def rotFun (c s : ℝ) (z : UnforcedLeray.Space) : UnforcedLeray.Space :=
  WithLp.toLp 2 ![c * z 0 - s * z 1, s * z 0 + c * z 1, z 2]

theorem rotFun_inv (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (z : UnforcedLeray.Space) :
    rotFun c (-s) (rotFun c s z) = z := by
  ext i
  fin_cases i
  · show c * (c * z 0 - s * z 1) - (-s) * (s * z 0 + c * z 1) = z 0
    linear_combination (z 0) * hcs
  · show (-s) * (c * z 0 - s * z 1) + c * (s * z 0 + c * z 1) = z 1
    linear_combination (z 1) * hcs
  · rfl

/-- The planar rotation as a linear isometry equivalence of `ℝ³`. -/
def rotEquiv (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space where
  toFun := rotFun c s
  invFun := rotFun c (-s)
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rotFun] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [rotFun] <;> ring
  left_inv := rotFun_inv c s hcs
  right_inv z := by
    have h' : c ^ 2 + (-s) ^ 2 = 1 := by linear_combination hcs
    have := rotFun_inv c (-s) h' z
    rwa [neg_neg] at this
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [rotFun, Fin.sum_univ_three]
    linear_combination (z 0 ^ 2 + z 1 ^ 2) * hcs

theorem rotExists_holds : RotExists := by
  intro y y' hr hz
  have hsq : ∀ w : UnforcedLeray.Space,
      UnforcedLeray.Short.PartIIIb.NearInst.hRad w ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    intro w
    unfold UnforcedLeray.Short.PartIIIb.NearInst.hRad
    exact Real.sq_sqrt (by positivity)
  have hE : y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [← hsq y', ← hsq y, hr]
  by_cases h0 : y 0 ^ 2 + y 1 ^ 2 = 0
  · -- the common point lies on the axis: `y = y'`
    have hy0 : y 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]) (sq_nonneg _))
    have hy1 : y 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]) (sq_nonneg _))
    have hy0' : y' 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]) (sq_nonneg _))
    have hy1' : y' 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]) (sq_nonneg _))
    refine ⟨LinearIsometryEquiv.refl ℝ UnforcedLeray.Space, ?_, fun z => ⟨rfl, rfl⟩⟩
    show y = y'
    ext i
    fin_cases i
    · show y 0 = y' 0
      rw [hy0, hy0']
    · show y 1 = y' 1
      rw [hy1, hy1']
    · show y 2 = y' 2
      exact hz
  · -- generic case: the planar rotation with the explicit `(c, s)`
    obtain ⟨c, hc⟩ : ∃ c : ℝ,
        c = (y 0 * y' 0 + y 1 * y' 1) / (y 0 ^ 2 + y 1 ^ 2) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ,
        s = (y 0 * y' 1 - y 1 * y' 0) / (y 0 ^ 2 + y 1 ^ 2) := ⟨_, rfl⟩
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      have hid : (y 0 * y' 0 + y 1 * y' 1) ^ 2 + (y 0 * y' 1 - y 1 * y' 0) ^ 2 =
          (y 0 ^ 2 + y 1 ^ 2) * (y' 0 ^ 2 + y' 1 ^ 2) := by ring
      rw [hc, hs, div_pow, div_pow, ← add_div, hid, hE]
      rw [div_eq_one_iff_eq (pow_ne_zero 2 h0)]
      ring
    refine ⟨rotEquiv c s hcs, ?_, fun z => ⟨?_, rfl⟩⟩
    · show rotFun c s y = y'
      ext i
      fin_cases i
      · show c * y 0 - s * y 1 = y' 0
        rw [hc, hs]
        field_simp
        ring
      · show s * y 0 + c * y 1 = y' 1
        rw [hc, hs]
        field_simp
        ring
      · show y 2 = y' 2
        exact hz
    · show UnforcedLeray.Short.PartIIIb.NearInst.hRad (rotFun c s z) =
        UnforcedLeray.Short.PartIIIb.NearInst.hRad z
      unfold UnforcedLeray.Short.PartIIIb.NearInst.hRad
      congr 1
      show (c * z 0 - s * z 1) ^ 2 + (s * z 0 + c * z 1) ^ 2 = z 0 ^ 2 + z 1 ^ 2
      linear_combination (z 0 ^ 2 + z 1 ^ 2) * hcs

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
