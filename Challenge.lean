import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

namespace MS

/-- Overlap conditions on the buyer/seller type intervals: each interval is
nontrivial and the two supports overlap in both directions. -/
def Overlap (a1 b1 a2 b2 : ℝ) : Prop :=
  a1 < b1 ∧ a2 < b2 ∧ a2 < b1 ∧ a1 < b2

/-- The full Myerson-Satterthwaite model: type intervals, atomless full-support
probability measures with positive densities, allocation and transfer rules,
ex post efficiency, Bayesian incentive compatibility, interim individual
rationality, and weak (ex ante) budget balance. -/
def IsModel (a1 b1 a2 b2 : ℝ) (mu nu : Measure ℝ)
    (q tb tc : ℝ × ℝ → ℝ) : Prop :=
  Overlap a1 b1 a2 b2 ∧
  IsProbabilityMeasure mu ∧
  IsProbabilityMeasure nu ∧
  MeasureTheory.NullSingletonClass mu ∧
  MeasureTheory.NullSingletonClass nu ∧
  Measure.support mu ⊆ Set.Icc a1 b1 ∧
  Measure.support nu ⊆ Set.Icc a2 b2 ∧
  Measure.AbsolutelyContinuous (volume.restrict (Set.Icc a1 b1)) mu ∧
  Measure.AbsolutelyContinuous (volume.restrict (Set.Icc a2 b2)) nu ∧
  (∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a1 b1).Nonempty → 0 < mu s) ∧
  (∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a2 b2).Nonempty → 0 < nu s) ∧
  AEStronglyMeasurable q (mu.prod nu) ∧
  (∀ v ∈ Set.Icc a1 b1, AEStronglyMeasurable (fun c => q (v, c)) nu) ∧
  (∀ c ∈ Set.Icc a2 b2, AEStronglyMeasurable (fun v => q (v, c)) mu) ∧
  (∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, 0 ≤ q (v, c)) ∧
  (∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, q (v, c) ≤ 1) ∧
  Integrable tb (mu.prod nu) ∧
  Integrable tc (mu.prod nu) ∧
  (∀ v ∈ Set.Icc a1 b1, Integrable (fun c => tb (v, c)) nu) ∧
  (∀ c ∈ Set.Icc a2 b2, Integrable (fun v => tc (v, c)) mu) ∧
  q =ᵐ[(mu.prod nu).restrict {p | p.2 < p.1}] (fun _ => (1 : ℝ)) ∧
  q =ᵐ[(mu.prod nu).restrict {p | p.1 < p.2}] (fun _ => (0 : ℝ)) ∧
  (∀ v ∈ Set.Icc a1 b1, ∀ v' ∈ Set.Icc a1 b1,
    interimU q tb nu v ≥ interimU q tb nu v' + (v - v') * interimQ q nu v') ∧
  (∀ c ∈ Set.Icc a2 b2, ∀ c' ∈ Set.Icc a2 b2,
    interimW q tc mu c ≥ interimW q tc mu c' + (c' - c) * interimR q mu c') ∧
  (∀ v ∈ Set.Icc a1 b1, 0 ≤ interimU q tb nu v) ∧
  (∀ c ∈ Set.Icc a2 b2, 0 ≤ interimW q tc mu c) ∧
  (∫ p, tc p ∂(mu.prod nu)) ≤ (∫ p, tb p ∂(mu.prod nu))

end MS

namespace MS.Palomar

/-- Myerson-Satterthwaite impossibility (continuous version): statement hole. -/
theorem myersonSatterthwaite (a1 b1 a2 b2 : ℝ) (mu nu : Measure ℝ)
    (q tb tc : ℝ × ℝ → ℝ) (h : MS.IsModel a1 b1 a2 b2 mu nu q tb tc) : False := by
  sorry

end MS.Palomar
