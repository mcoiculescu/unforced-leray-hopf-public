import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal
import UnforcedLeray.Units.B0224.Semigroup
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# `CausalEqDuhamel` from two analytic leaves

Source `the November 2 reference manuscript`
1650-1656, 1684-1689.  `causalHeat Gh = duhamel G` a.e. on the cell.  The vector Bochner integral
`causalHeat` equals the vector of the scalar `duhamel` integrals only when the scalar integrands
are integrable (leaf `DuhamelIntegrable`); and `planeHeat` of the `H_g` representative equals the
vector of `planeHeat`s of the components of `G` because the slice is a.e. equal to a bounded
function (leaf `PlaneHeatVecAe`).  Proved here: the slicing in `σ`, the `q`-periodic recentring
`cellPt`, and the assembly (`causalEqDuhamel_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Leaf 1 (source 1650-1656, `planeHeat_of_pos`): if the slice `periodize c Gh (σ,·)` is a.e. equal
to the vector `(G(σ,·) i)_i` with `G` bounded measurable, then for `σ < s` (heat time `ν(s-σ) > 0`)
the cylinder heat of the slice is the vector of the cylinder heats of the components. -/
def PlaneHeatVecAe : Prop :=
  ∀ (c ν : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν →
    ∀ Gh : UnforcedLeray.B0220.HgSpace c UnforcedLeray.B0223.MeridC, ∀ σ s : ℝ, σ < s →
      (∀ i : Fin 2, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
        UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z) i = (G (σ, z) i : ℂ)) →
      ∀ x : ℝ × ℝ,
        UnforcedLeray.B0224.planeHeat (ν * (s - σ))
            (fun z => UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z)) x =
          WithLp.toLp 2 (fun i : Fin 2 =>
            UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x)

/-- Leaf 2 (source 1684-1689): the scalar Duhamel integrand is interval integrable on `(0,s)`.
`G` vanishes for `σ < s₀` (so the factor `(σ/s)^μ` is harmless), is jointly continuous, and
`planeHeat θ (G(σ,·) i)` is bounded by `sup |G|` (Gaussian mass `1`) and measurable in `σ` on
`(0,s)` (parametric integral). -/
def DuhamelIntegrable : Prop :=
  ∀ (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ s : ℝ, 0 < s →
    ∀ (x : ℝ × ℝ) (i : Fin 2),
      IntervalIntegrable (fun σ : ℝ => (((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) •
        UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x)
        volume 0 s

theorem duhamel_cellPt (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ)
    (hper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η))) (p : UnforcedLeray.B0220.Profile)
    (i : Fin 2) : duhamel ν μ G (NearInst.cellPt c p) i = duhamel ν μ G p i := by
  unfold NearInst.cellPt
  split_ifs with h
  · rfl
  · unfold duhamel
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp only
    congr 1
    have hu : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => ((G (σ, z) i : ℝ) : ℂ)) := by
      intro z
      simp only [hper σ z.1 z.2]
    have hp := UnforcedLeray.B0224.isPeriodic_planeHeat (θ := ν * (p.1 - σ)) hu (p.2.1 - c, p.2.2)
    simpa using hp.symm

theorem causalEqDuhamel_of (h1 : PlaneHeatVecAe) (h2 : DuhamelIntegrable) : CausalEqDuhamel := by
  intro c ν μ hc hν G hG Gh hs
  have hmem : ∀ᵐ p ∂(UnforcedLeray.B0220.measureH c), p ∈ UnforcedLeray.B0220.cell c :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c))
  filter_upwards [hmem] with p hp
  have hs0 : 0 < p.1 := hp.1
  have hs' : ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 2, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z) i = (G (σ, z) i : ℂ) := ae_all_iff.2 hs
  have hs'' := (ae_restrict_iff' measurableSet_Ioi).1 hs'
  have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∉ ({p.1} : Set ℝ) :=
    (Set.countable_singleton p.1).ae_notMem volume
  have hcong : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ι (0 : ℝ) p.1 →
      (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) • UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
          (fun z => UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z)) p.2 =
        WithLp.toLp 2 (fun i : Fin 2 => (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) •
          UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) p.2) := by
    filter_upwards [hs'', hne] with σ hσ hn hI
    rw [Set.uIoc_of_le hs0.le] at hI
    have hlt : σ < p.1 := lt_of_le_of_ne hI.2 (by simpa using hn)
    rw [h1 c ν G hG hν Gh σ p.1 hlt (hσ hI.1) p.2]
    ext i
    simp
  have hint : ∀ i : Fin 2, IntegrableOn (fun σ : ℝ => (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) •
      UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) p.2)
      (Ioc 0 p.1) volume := fun i =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs0.le).1 (h2 c ν μ G hG hν p.1 hs0 p.2 i)
  have e1 : UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (⇑Gh) p =
      ∫ σ in Ioc 0 p.1, WithLp.toLp 2 (fun i : Fin 2 => (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) •
        UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) p.2) := by
    unfold UnforcedLeray.B0225.causalHeat
    rw [intervalIntegral.integral_congr_ae (g := fun σ => WithLp.toLp 2 (fun i : Fin 2 =>
      (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) •
        UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) p.2))
      (by simpa using hcong), intervalIntegral.integral_of_le hs0.le]
  rw [e1]
  ext i
  rw [eval_integral_piLp (μ := volume.restrict (Ioc 0 p.1))
    (f := fun σ : ℝ => (WithLp.toLp 2 (fun i : Fin 2 => (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) •
      UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) p.2) :
        UnforcedLeray.B0223.MeridC)) (fun i => hint i)]
  simp only
  rw [duhamel_cellPt c ν μ G hG.2.1 p i, duhamel, intervalIntegral.integral_of_le hs0.le]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
