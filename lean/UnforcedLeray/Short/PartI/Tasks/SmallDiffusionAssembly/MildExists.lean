import UnforcedLeray.Short.PartI.Sub.PartI_C05
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.ComplementDysonFamily

/-!
# Target `PartI:C05/1`: existence of the mild complementary evolution

Source of record: `the November 2 reference manuscript`, lines 1014-1030
("the evolution exists for measurable `β` by the Dyson series based on `exp(D∫β)`").

On the block `[s,t]` the base family is `e^{D∫β}` (`fdsFam`) and the bounded perturbation is the
sum of the free coefficient `T - λ - βκ` (`fdsA`) and the complementary interaction
(`complementInteraction`); its Dyson sum, restricted to `[s,r]`, does not depend on the block.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Infra.Dunford (rankOneProj)

section
variable (lam kappa : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG) (Rf : B0010.XG →L[ℂ] B0010.XG)
  (β : ℝ → ℝ) (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)

/-- The total bounded perturbation on the block `[s,t]`. -/
def mcPert (s t : ℝ) : UnforcedLeray.Evolution.BoundedPert B0010.XG s t :=
  UnforcedLeray.Evolution.boundedPertSum (fdsA lam kappa s t 1 β hβm hβ)
    (UnforcedLeray.Evolution.BoundedPert.ofAEStronglyMeasurable
      (complementInteraction l q Rf β)
      (aestronglyMeasurable_complementInteraction l q Rf hβm _)
      ⟨‖Planar.L0 - complementT - rankOneProj l q‖ + 1 * ‖Rf‖,
        fun r _ => norm_complementInteraction_le l q Rf hβ r⟩)

/-- The Dyson evolution on the block `[s,t]`. -/
def mcBlock (s t : ℝ) : UnforcedLeray.Evolution.EvolutionFamily B0010.XG s t :=
  UnforcedLeray.Evolution.dyson (fdsFam s t 1 β hβm hβ) (mcPert lam kappa l q Rf β hβm hβ s t)

theorem mcBlock_U (s t : ℝ) :
    (mcBlock lam kappa l q Rf β hβm hβ s t).U =
      UnforcedLeray.Evolution.dysonU (fdsFam s t 1 β hβm hβ)
        (mcPert lam kappa l q Rf β hβm hβ s t) := rfl

theorem mcBlock_indep {s r b : ℝ} (hsr : s ≤ r) (hrb : r ≤ b) (x : B0010.XG) :
    (mcBlock lam kappa l q Rf β hβm hβ s r).U r s x =
      (mcBlock lam kappa l q Rf β hβm hβ s b).U r s x := by
  rw [mcBlock_U, mcBlock_U,
    UnforcedLeray.Evolution.dysonU_apply _ _ (le_refl s) hsr le_rfl x,
    UnforcedLeray.Evolution.dysonU_apply _ _ (le_refl s) hsr hrb x]
  exact tsum_congr fun k => fdeAux_dysonTerm_congr (fdsFam s r 1 β hβm hβ)
    (mcPert lam kappa l q Rf β hβm hβ s r) (fdsFam s b 1 β hβm hβ)
    (mcPert lam kappa l q Rf β hβm hβ s b) (fun _ _ => rfl) (fun _ => rfl) k r s x

/-- The candidate evolution. -/
def mcF (t s : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  if s ≤ t then (mcBlock lam kappa l q Rf β hβm hβ s t).U t s else 1

theorem mcF_eq_block {s t b : ℝ} (hst : s ≤ t) (htb : t ≤ b) (x : B0010.XG) :
    mcF lam kappa l q Rf β hβm hβ t s x = (mcBlock lam kappa l q Rf β hβm hβ s b).U t s x := by
  unfold mcF
  rw [if_pos hst]
  exact mcBlock_indep lam kappa l q Rf β hβm hβ hst htb x

theorem mcF_self (t : ℝ) : mcF lam kappa l q Rf β hβm hβ t t = 1 := by
  unfold mcF
  rw [if_pos (le_refl t), mcBlock_U]
  exact UnforcedLeray.Evolution.dysonU_diag _ _ (Set.left_mem_Icc.mpr le_rfl)

theorem mcF_cont (x : B0010.XG) (s : ℝ) :
    ContinuousOn (fun t => mcF lam kappa l q Rf β hβm hβ t s x) (Ici s) := by
  intro t₀ ht₀
  have hst₀ : s ≤ t₀ := Set.mem_Ici.mp ht₀
  have hlt : t₀ < t₀ + 1 := lt_add_one t₀
  have hc : ContinuousOn (fun t => UnforcedLeray.Evolution.dysonU
      (fdsFam s (t₀ + 1) 1 β hβm hβ) (mcPert lam kappa l q Rf β hβm hβ s (t₀ + 1)) t s x)
      (Icc s (t₀ + 1)) :=
    UnforcedLeray.Evolution.continuousOn_dysonU_fst _ _ x (le_refl s)
  have hcongr : ContinuousOn (fun t => mcF lam kappa l q Rf β hβm hβ t s x)
      (Icc s (t₀ + 1)) := by
    refine hc.congr fun t ht => ?_
    show mcF lam kappa l q Rf β hβm hβ t s x = UnforcedLeray.Evolution.dysonU
      (fdsFam s (t₀ + 1) 1 β hβm hβ) (mcPert lam kappa l q Rf β hβm hβ s (t₀ + 1)) t s x
    rw [mcF_eq_block lam kappa l q Rf β hβm hβ ht.1 ht.2 x, mcBlock_U]
  have hmem : Icc s (t₀ + 1) ∈ 𝓝[Ici s] t₀ :=
    mem_nhdsWithin.mpr ⟨Iio (t₀ + 1), isOpen_Iio, Set.mem_Iio.mpr hlt,
      fun t ht => ⟨Set.mem_Ici.mp ht.2, le_of_lt (Set.mem_Iio.mp ht.1)⟩⟩
  exact (hcongr t₀ ⟨hst₀, hlt.le⟩).mono_of_mem_nhdsWithin hmem

/-- The generator of `IsMildComplementEvolution`. -/
def mcGen (r : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
    (β r * kappa) • (1 : B0010.XG →L[ℂ] B0010.XG) + (β r : ℂ) • Rf

theorem mcPert_A (s t r : ℝ) : (mcPert lam kappa l q Rf β hβm hβ s t).A r = mcGen lam kappa l q Rf β r := by
  rw [mcGen, complementDyson_gen]
  rfl

theorem mcFree_apply (s t : ℝ) (x : B0010.XG) :
    (fdsFam s t 1 β hβm hβ).U t s x = B0123.expD (∫ u in s..t, β u) x := rfl

theorem mcPt {s t r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t) (x : B0010.XG) :
    (fdsFam s t 1 β hβm hβ).U t r
        ((mcPert lam kappa l q Rf β hβm hβ s t).A r
          ((mcBlock lam kappa l q Rf β hβm hβ s t).U r s x)) =
      B0123.expD (∫ u in r..t, β u)
        (mcGen lam kappa l q Rf β r (mcF lam kappa l q Rf β hβm hβ r s x)) := by
  rw [mcF_eq_block lam kappa l q Rf β hβm hβ hsr hrt x, mcPert_A]
  rfl

theorem mcF_integrable (s t : ℝ) (hst : s ≤ t) (x : B0010.XG) :
    IntervalIntegrable (fun r => B0123.expD (∫ u in r..t, β u)
      (mcGen lam kappa l q Rf β r (mcF lam kappa l q Rf β hβm hβ r s x))) volume s t := by
  refine (UnforcedLeray.Evolution.intervalIntegrable_dysonU (fdsFam s t 1 β hβm hβ)
    (mcPert lam kappa l q Rf β hβm hβ s t) (le_refl s) hst le_rfl x).congr_ae
    (ae_restrict_of_forall_mem measurableSet_uIoc fun r hr => ?_)
  rw [uIoc_of_le hst] at hr
  exact mcPt lam kappa l q Rf β hβm hβ hr.1.le hr.2 x

theorem mcF_duhamel (s t : ℝ) (hst : s ≤ t) (x : B0010.XG) :
    mcF lam kappa l q Rf β hβm hβ t s x = B0123.expD (∫ u in s..t, β u) x +
      ∫ r in s..t, B0123.expD (∫ u in r..t, β u)
        (mcGen lam kappa l q Rf β r (mcF lam kappa l q Rf β hβm hβ r s x)) := by
  have hD := UnforcedLeray.Evolution.dyson_left (fdsFam s t 1 β hβm hβ)
    (mcPert lam kappa l q Rf β hβm hβ s t) ⟨le_refl s, hst, le_rfl⟩ x
  rw [mcF_eq_block lam kappa l q Rf β hβm hβ hst le_rfl x]
  show (UnforcedLeray.Evolution.dyson (fdsFam s t 1 β hβm hβ)
    (mcPert lam kappa l q Rf β hβm hβ s t)).U t s x = _
  rw [hD, mcFree_apply]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hst] at hr
  exact mcPt lam kappa l q Rf β hβm hβ hr.1 hr.2 x

end

/-- **Target `PartI:C05/1`** (source lines 1014-1030). -/
theorem mildComplementExists : MildComplementExists := by
  intro lam q l _ qd _ hq hqd β hβm hβ
  refine ⟨mcF lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β hβm hβ, ?_⟩
  exact
    { self_eq := fun t => mcF_self _ _ _ _ _ _ hβm hβ t
      cont := fun s x => mcF_cont _ _ _ _ _ _ hβm hβ x s
      integrable := fun s t hst x => mcF_integrable _ _ _ _ _ _ hβm hβ s t hst x
      duhamel := fun s t hst x => mcF_duhamel _ _ _ _ _ _ hβm hβ s t hst x }

end UnforcedLeray.Short.PartI
