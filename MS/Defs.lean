import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.OuterMeasure.AE

open MeasureTheory

noncomputable def interimQ (q : ℝ × ℝ → ℝ) (nu : Measure ℝ) (v : ℝ) : ℝ :=
  ∫ c, q (v, c) ∂nu

noncomputable def interimR (q : ℝ × ℝ → ℝ) (mu : Measure ℝ) (c : ℝ) : ℝ :=
  ∫ v, q (v, c) ∂mu

noncomputable def interimU (q tb : ℝ × ℝ → ℝ) (nu : Measure ℝ) (v : ℝ) : ℝ :=
  ∫ c, (v * q (v, c) - tb (v, c)) ∂nu

noncomputable def interimW (q tc : ℝ × ℝ → ℝ) (mu : Measure ℝ) (c : ℝ) : ℝ :=
  ∫ v, (tc (v, c) - c * q (v, c)) ∂mu

/-- The data and hypotheses for a continuous bilateral-trade instance. -/
structure MSData where
  a1 : ℝ
  b1 : ℝ
  a2 : ℝ
  b2 : ℝ
  h1 : a1 < b1
  h2 : a2 < b2
  h3 : a2 < b1
  mu : Measure ℝ
  nu : Measure ℝ
  mu_probability : IsProbabilityMeasure mu
  nu_probability : IsProbabilityMeasure nu
  mu_noAtoms : MeasureTheory.NullSingletonClass mu
  nu_noAtoms : MeasureTheory.NullSingletonClass nu
  mu_supported : Measure.support mu ⊆ Set.Icc a1 b1
  nu_supported : Measure.support nu ⊆ Set.Icc a2 b2
  mu_fullSupport : ∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a1 b1).Nonempty → 0 < mu s
  nu_fullSupport : ∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a2 b2).Nonempty → 0 < nu s
  q : ℝ × ℝ → ℝ
  q_measurable : AEStronglyMeasurable q (mu.prod nu)
  q_sectionB : ∀ v ∈ Set.Icc a1 b1, AEStronglyMeasurable (fun c => q (v, c)) nu
  q_sectionS : ∀ c ∈ Set.Icc a2 b2, AEStronglyMeasurable (fun v => q (v, c)) mu
  q_nonneg : ∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, 0 ≤ q (v, c)
  q_le_one : ∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, q (v, c) ≤ 1
  tb : ℝ × ℝ → ℝ
  tc : ℝ × ℝ → ℝ
  tb_integrable : Integrable tb (mu.prod nu)
  tc_integrable : Integrable tc (mu.prod nu)
  tb_section : ∀ v ∈ Set.Icc a1 b1, Integrable (fun c => tb (v, c)) nu
  tc_section : ∀ c ∈ Set.Icc a2 b2, Integrable (fun v => tc (v, c)) mu
  effB : q =ᵐ[(mu.prod nu).restrict {p | p.2 < p.1}] (fun _ => (1 : ℝ))
  effS : q =ᵐ[(mu.prod nu).restrict {p | p.1 < p.2}] (fun _ => (0 : ℝ))
  bicB : ∀ v ∈ Set.Icc a1 b1, ∀ v' ∈ Set.Icc a1 b1,
    interimU q tb nu v ≥ interimU q tb nu v' + (v - v') * interimQ q nu v'
  bicS : ∀ c ∈ Set.Icc a2 b2, ∀ c' ∈ Set.Icc a2 b2,
    interimW q tc mu c ≥ interimW q tc mu c' + (c' - c) * interimR q mu c'
  irB : ∀ v ∈ Set.Icc a1 b1, 0 ≤ interimU q tb nu v
  irS : ∀ c ∈ Set.Icc a2 b2, 0 ≤ interimW q tc mu c
  bb : (∫ p, tc p ∂(mu.prod nu)) ≤ (∫ p, tb p ∂(mu.prod nu))

namespace MSData

/-- The buyer's interim trade probability at value `v`. -/
noncomputable def Q (D : MSData) (v : ℝ) : ℝ := interimQ D.q D.nu v

/-- The seller's interim trade probability at cost `c`. -/
noncomputable def R (D : MSData) (c : ℝ) : ℝ := interimR D.q D.mu c

/-- The buyer's interim utility at value `v`. -/
noncomputable def U (D : MSData) (v : ℝ) : ℝ := interimU D.q D.tb D.nu v

/-- The seller's interim utility at cost `c`. -/
noncomputable def W (D : MSData) (c : ℝ) : ℝ := interimW D.q D.tc D.mu c

@[simp] theorem Q_def (D : MSData) (v : ℝ) :
    D.Q v = interimQ D.q D.nu v := rfl

@[simp] theorem R_def (D : MSData) (c : ℝ) :
    D.R c = interimR D.q D.mu c := rfl

@[simp] theorem U_def (D : MSData) (v : ℝ) :
    D.U v = interimU D.q D.tb D.nu v := rfl

@[simp] theorem W_def (D : MSData) (c : ℝ) :
    D.W c = interimW D.q D.tc D.mu c := rfl

theorem bicB' (D : MSData) : ∀ v ∈ Set.Icc D.a1 D.b1, ∀ v' ∈ Set.Icc D.a1 D.b1,
    D.U v ≥ D.U v' + (v - v') * D.Q v' := by
  intro v hv v' hv'
  simpa only [U_def, Q_def] using D.bicB v hv v' hv'

theorem bicS' (D : MSData) : ∀ c ∈ Set.Icc D.a2 D.b2, ∀ c' ∈ Set.Icc D.a2 D.b2,
    D.W c ≥ D.W c' + (c' - c) * D.R c' := by
  intro c hc c' hc'
  simpa only [W_def, R_def] using D.bicS c hc c' hc'

theorem irB' (D : MSData) : ∀ v ∈ Set.Icc D.a1 D.b1, 0 ≤ D.U v := by
  intro v hv
  simpa only [U_def] using D.irB v hv

theorem irS' (D : MSData) : ∀ c ∈ Set.Icc D.a2 D.b2, 0 ≤ D.W c := by
  intro c hc
  simpa only [W_def] using D.irS c hc

end MSData
