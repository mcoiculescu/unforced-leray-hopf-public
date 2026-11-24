import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2

/-!
# Part II-b, task `PartII-b:T13/1/4/2/7` (`ChmCoreDeriv`): derivatives on the core

Source `the November 2 reference manuscript` lines 1933-1935 and 1377-1424.
On the core `q ∈ (0, N c)` the cutoff satisfies `ζ = 1` on an open interval, so `ζ(q) w` agrees
with `w` in a neighbourhood of every core point; hence all spatial derivatives up to order two
of `chmU ζ w` and `w` agree on the core (pure calculus).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology

/-- Where `ζ = 1` on the open `q`-interval containing `y.2.1`, `chmU ζ w` agrees with `w` near `y`. -/
lemma chm_U_eventually_eq (ζ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (hone : ∀ t ∈ Ioo (0 : ℝ) ((N : ℝ) * c), ζ t = 1)
    (w : Coord → ℂ) (y : Coord) (hy : y.2.1 ∈ Ioo (0 : ℝ) ((N : ℝ) * c)) :
    chmU ζ w =ᶠ[𝓝 y] w := by
  have hVo : IsOpen ((fun z : Coord => z.2.1) ⁻¹' Ioo (0 : ℝ) ((N : ℝ) * c)) :=
    isOpen_Ioo.preimage (by fun_prop)
  filter_upwards [hVo.mem_nhds hy] with z hz
  unfold chmU
  rw [hone z.2.1 hz]
  simp

theorem chmCoreDeriv : UnforcedLeray.Short.IIb.ChmCoreDeriv := by
  intro K c N hN ζ hζ w hw x hx
  obtain ⟨-, -, hone, -, -, -⟩ := hζ
  have hx' : x.2.1 ∈ Ioo (0 : ℝ) ((N : ℝ) * c) := hx
  have hone' : ∀ t ∈ Ioo (0 : ℝ) ((N : ℝ) * c), ζ t = 1 :=
    fun t ht => hone t (Ioo_subset_Icc_self ht)
  have hVo : IsOpen ((fun z : Coord => z.2.1) ⁻¹' Ioo (0 : ℝ) ((N : ℝ) * c)) :=
    isOpen_Ioo.preimage (by fun_prop)
  have hpt : ∀ j : Fin 3, ∀ y : Coord, y.2.1 ∈ Ioo (0 : ℝ) ((N : ℝ) * c) →
      cdv j (chmU ζ w) y = cdv j w y := by
    intro j y hy
    show fderiv ℝ (chmU ζ w) y (cdir j) = fderiv ℝ w y (cdir j)
    rw [(chm_U_eventually_eq ζ c N hone' w y hy).fderiv_eq]
  refine ⟨hpt 0 x hx', fun i j => ?_⟩
  have hEq : cdv j.succ (chmU ζ w) =ᶠ[𝓝 x] cdv j.succ w := by
    filter_upwards [hVo.mem_nhds hx'] with y hy
    exact hpt j.succ y hy
  show fderiv ℝ (cdv j.succ (chmU ζ w)) x (cdir i.succ) =
    fderiv ℝ (cdv j.succ w) x (cdir i.succ)
  rw [hEq.fderiv_eq]

end UnforcedLeray.Short.IIb
