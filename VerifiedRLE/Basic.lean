-- Run-Length Encoding (RLE)
-- Each run is represented as (count, value).
abbrev Run := Nat × Nat

/--
Decodes an RLE representation into the original list.

Each (count, value) pair is expanded into `count` copies
of `value`, then concatenated with the remaining decoded list.
-/

def decode : List Run → List Nat
  | [] => []
  | (count, value) :: rest =>
      List.replicate count value ++ decode rest

#eval decode [(3, 4), (2, 5)]
#eval decode [(1, 7)]
#eval decode []

/--
Encodes a list of natural numbers using Run-Length Encoding.

Recursively encodes the remaining list, then compares the
current element with the first encoded run.
If the values match, increase the count; otherwise, create a new run.
-/


def encode : List Nat → List Run
  | [] => []
  | x :: xs =>
      match encode xs with
      | [] => [(1, x)]
      | (count, value) :: rest =>
          if x == value then
            (count + 1, value) :: rest
          else
            (1, x) :: (count, value) :: rest


-- Encoder tests
#eval encode [4, 4, 4, 5, 5]
#eval encode [1, 2, 3]
#eval encode [7, 7, 7, 7]
#eval encode [1, 2, 1]
#eval encode []

-- Decoder + Encoder tests
#eval decode (encode [4, 4, 4, 5, 5])
#eval decode (encode [1, 2, 3])
#eval decode (encode [])



/--
Checks whether an RLE representation is canonical:
all counts are positive, and adjacent runs have different values.
since unvalid content would affect our decoding process.
For example, [(0,4),(2,5)] --> can't be valid input, since we don't have any 4 inside.
Otherwords, if we consider it as valid , we can write any numbers as combination of zero times.
-/

def validRLE : List Run → Bool
  | [] => true
  | [(count, _)] => count > 0
  | (count₁, value₁) :: (count₂, value₂) :: rest =>
      (count₁ > 0) &&
      (value₁ != value₂) &&
      validRLE ((count₂, value₂) :: rest)

#eval validRLE [(3, 4), (2, 5)]
#eval validRLE [(1, 4), (2, 4)]
#eval validRLE [(0, 4)]
#eval validRLE []


/--
Losslessness of RLE:
Decoding an encoded list reconstructs the original input.
-/


theorem de_encode_losslessness (xs : List Nat) :
    decode (encode xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs h_tail =>
      cases h : encode xs with
      | nil =>
          have hxs : xs = [] := by
            simpa [h, decode] using h_tail.symm
          simp [hxs, encode, decode]

      | cons run rest =>
          cases run with
          | mk count value =>
              have hdecode : decode ((count, value) :: rest) = xs := by
                simpa [h] using h_tail

              by_cases hv : x = value
              ·  --Case 1: same number as next token
                simp [encode, h, hv, decode, List.replicate_succ]
                rw [← hdecode]
                simp [decode]

              · --Case 2: different number as next token
                simp [encode, h, hv, decode]
                rw [← hdecode]
                simp [decode]

/--
Canonical representation:
Encoding a decoded valid RLE representation
reconstructs the original runs.
-/

/-helper method : encode a non-empty list of identical value, we run only once -/
theorem encode_replicate_succ (n value : Nat) :
    encode (List.replicate (n + 1) value) =
      [(n + 1, value)] := by
  induction n with
  | zero =>
      simp [encode]
  | succ n ih =>
      rw [List.replicate_succ, encode]
      simp [ih]


theorem encode_replicate_append
    (n value : Nat)
    (suffix : List Nat)
    (nextCount nextValue : Nat)
    (rest : List Run)
    (henc : encode suffix =
      (nextCount, nextValue) :: rest)
    (hne : value ≠ nextValue) :
    encode (List.replicate (n + 1) value ++ suffix) =
      (n + 1, value) :: (nextCount, nextValue) :: rest := by
  induction n with
  | zero =>
      simp [encode, List.replicate_succ, henc, hne]
  | succ n ih =>
      rw [List.replicate_succ]
      simp [encode, ih]


theorem en_decode_canonical {input : List Run}
    (hvalid : validRLE input = true) :
    encode (decode input) = input := by
  induction input generalizing hvalid with
  | nil =>
      rfl

  | cons head tail ih =>
      cases head with
      | mk count value =>
          cases tail with

          | nil =>
            cases count with
            | zero =>
              simp [validRLE] at hvalid
            | succ n =>
              simpa [decode] using
                (encode_replicate_succ n value)

          | cons nextRun rest =>
              cases nextRun with
              | mk nextCount nextValue =>
                  have hparts := hvalid
                  simp only [validRLE, Bool.and_eq_true] at hparts

                  have htail :
                      validRLE ((nextCount, nextValue) :: rest) = true := by
                    exact hparts.2

                  have htail_encode :
                      encode (decode ((nextCount, nextValue) :: rest)) =
                        (nextCount, nextValue) :: rest := by
                    exact ih htail

                  have hcount : count > 0 := by
                    simpa using hparts.1.1

                  have hne : value ≠ nextValue := by
                    simpa using hparts.1.2

                  sorry
