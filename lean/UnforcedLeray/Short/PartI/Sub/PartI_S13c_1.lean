import UnforcedLeray.Short.PartI.Tasks.EulerRegularityTransfer.Defs
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM
import UnforcedLeray.Short.PartI.Tasks.InteractionCompactHjM
import UnforcedLeray.Lib.PlanarSectorsB.TransportDuhamel

/-!
# Part I, task `PartI:S13c/1`: decomposition of `euler_evolution_HjM_exists`

Source of record: `the November 2 reference manuscript`,
lines 853-863 ("The bounded perturbation theorem now realizes `𝓛` ... Both terms have zero
integral, so `𝒳_{j,M}` is invariant").

Proof plan: the Dyson series for the free transport group `T` of `PartI:S13a` perturbed by the
compact interaction `T₀` of `PartI:S13b` gives `S` on `H^j_M` with the Duhamel identity
(`DysonBoundedPertHjM`).  Applying the bounded map `value : H^j_M → L²_M` (intertwining lemmas
`TransportIntertwineHjM`, `CouplingIntertwineHjM`) turns this into the `L²_M` Duhamel equation,
whose unique solution is `Planar.eulerGroupW` (`DuhamelUniqueL2w`).  Group law, continuity and
invariance of `𝒳_{j,M}` follow.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Dyson/Duhamel existence** (source lines 858-860, "bounded perturbation theorem"): for a free
transport group `T` on `H^j_M` (strongly continuous, polynomially bounded) and any bounded `K`,
there is a strongly continuous family `S` with `S t F = T t F + ∫₀ᵗ T(t-s) K S(s) F ds`, the
integrand being continuous in `s`. -/
def DysonBoundedPertHjM (j : ℕ) {M : ℝ} : Prop :=
  ∀ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M), IsFreeTransportGroupHjM j T →
    ∀ K : B0008.HjM j M →L[ℂ] B0008.HjM j M,
      ∃ S : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
        (∀ F, Continuous fun t => S t F) ∧
        (∀ t F, Continuous fun s : ℝ => T (t - s) (K (S s F))) ∧
        ∀ t F, S t F = T t F + ∫ s in (0 : ℝ)..t, T (t - s) (K (S s F))

/-- The free transport group on `H^j_M` is the restriction of `Planar.transportGroupW`
(`freeFlow`, source lines 841-852): `value (T t F) = transportGroupW t (value F)`. -/
def TransportIntertwineHjM (j : ℕ) {M : ℝ} (_hM : 1 < M) : Prop :=
  ∀ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M), IsFreeTransportGroupHjM j T →
    ∀ t F, (T t F).value = Planar.transportGroupW M t F.value

/-- The interaction `T₀` (the Biot-Savart term `B0009.perturbation`, source lines 853-857) is the
restriction of `-Planar.couplingW`: `value (T₀ F) = -couplingW (value F)`, since
`Planar.couplingW` is the sector form of `A_E = -(Kf)·∇E₀` (sign fixed by `secProfAE`). -/
def CouplingIntertwineHjM (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ T₀ : B0008.HjM j M →L[ℂ] B0008.HjM j M,
    (∀ F : B0008.HjM j M, ((T₀ F).value : ℂ → ℂ) =ᵐ[volume] B0009.perturbation (F.value : ℂ → ℂ)) →
    ∀ F, (T₀ F).value = -Planar.couplingW hM F.value

/-- **Gronwall uniqueness in `L²_M`** (source lines 858-860): a continuous solution of the Duhamel
equation `u t = T(t) f + ∫₀ᵗ T(t-τ) A_E u(τ) dτ` is `e^{t𝓛} f = Planar.eulerGroupW hM t f`. -/
def DuhamelUniqueL2w {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ (f : Planar.L2w M) (u : ℝ → Planar.L2w M), Continuous u →
    (∀ t, u t = Planar.transportGroupW M t f +
      ∫ τ in (0 : ℝ)..t, Planar.transportGroupW M (t - τ) (Planar.couplingW hM (u τ))) →
    ∀ t, u t = Planar.eulerGroupW hM t f

theorem euler_evolution_HjM_exists_of (j : ℕ) {M : ℝ} (hM : 1 < M)
    (hD : DysonBoundedPertHjM j (M := M)) (hT : TransportIntertwineHjM j hM)
    (hK : CouplingIntertwineHjM j hM) (hU : DuhamelUniqueL2w hM) :
    EulerEvolutionHjMExists j hM := by
  obtain ⟨T, hTa, hTb, hTc, hTd, hTe, -⟩ := transport_group_HjM j hM
  have hTfree : IsFreeTransportGroupHjM j T := ⟨hTa, hTb, hTc, hTd, hTe⟩
  obtain ⟨-, T₀, -, hT₀, hT₀X⟩ := interaction_isCompactOperator_HjM j hM
  obtain ⟨S, hSc, hSi, hSd⟩ := hD T hTfree (-T₀)
  have hid : ∀ t F, (S t F).value = Planar.eulerGroupW hM t F.value := by
    intro t F
    have hu := hU F.value (fun s => (S s F).value)
      ((B0008.HjM.valueCLM j M).continuous.comp (hSc F)) (by
        intro t
        have h1 := congrArg (B0008.HjM.valueCLM j M) (hSd t F)
        rw [map_add, ← (B0008.HjM.valueCLM j M).intervalIntegral_comp_comm
          ((hSi t F).intervalIntegrable 0 t)] at h1
        simp only [B0008.HjM.valueCLM_apply] at h1
        have e1 : ∀ s, (T (t - s) ((-T₀) ((S s) F))).value =
            Planar.transportGroupW M (t - s) (Planar.couplingW hM ((S s F).value)) := fun s => by
          have hv : ((-T₀) ((S s) F)).value = Planar.couplingW hM ((S s F).value) := by
            rw [neg_apply]
            show -(T₀ ((S s) F)).value = _
            rw [hK T₀ hT₀]
            exact neg_neg _
          rw [hT T hTfree, hv]
        simp only [e1] at h1
        rw [h1, hT T hTfree t F]
        rfl)
    exact hu t
  refine ⟨S, ⟨fun t F => ?_, fun s t => ?_, ?_, hSc⟩, fun t F hF => ?_⟩
  · rw [hid]
    exact Filter.EventuallyEq.rfl
  · ext F : 2
    rw [mul_apply_eq_comp, hid, hid, hid, Planar.eulerGroupW_add]
    rfl
  · ext F : 2
    rw [hid, Planar.eulerGroupW_zero]
    rfl
  · rw [B0008.mem_XjM_iff hM]
    have h0 := (B0008.mem_XjM_iff hM F).1 hF
    have hmem : F.value ∈ Planar.X0 hM := (Planar.mem_X0_iff hM _).2 h0
    have := Planar.eulerGroupW_mem_X0 hM t _ hmem
    rw [Planar.mem_X0_iff] at this
    rw [hid]
    exact this

end UnforcedLeray.Short.PartI
