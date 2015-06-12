module AES

import Data.Bits
import Data.Vect
import Data.Fin

import Debug.Trace

Nb : Nat
Nb = 4

-- mmm unicode 2^8 ?
GF28 : Type
GF28 = Bits 8

instance Num GF28 where
  a + b = xor a b
  a - b = xor a b
  a * b = xor a b
  abs = id
  fromInteger = intToBits

State : Type
State = Vect 4 (Vect Nb GF28)

-- Enforcing non zero vectors. Yay dependent types.
gf28Add : Vect (S n) GF28 -> GF28
gf28Add = foldr1 xor

irreducible : GF28
irreducible = 0x1b

go : GF28 -> GF28 -> GF28 -> Int -> GF28
go a b p n = trace (show (a,b,p,n)) 
             (if a == 0 || b == 0 || n == 7 then
                p
             else go (xor (if getBit 7 a then irreducible else 0) (shiftLeft a 1))
                     (shiftRightLogical b 1)
                     (xor p (if getBit 0 b then a else 0))
                     (n + 1))

gf28Mult : GF28 -> GF28 -> GF28
gf28Mult x y = go x y 0 0

