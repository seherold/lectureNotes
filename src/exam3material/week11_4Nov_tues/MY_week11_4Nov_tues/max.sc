// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = Z.prompt("Enter first number: ")
val y: Z = Z.prompt("Enter second number: ")

//x = 3, y = 4

//how do we assume x is bigger than y?
assume( x > y )

//don't need a deduce block here, could have one but don't need it because x and y don't change before val max: Z = x


val max: Z = x

Deduce(
    1 ( x > y ) by Premise,
    2 ( max == x )by Premise,
    3 (max >= x) by Algebra*(2),
    4 (max == x | max == y) by OrI1(2),
    5 (max >= y) by Algebra*(1,2)
)


//what can we put in a proof block here?

//how do we assert max is the biggest between our two inputs?
assert(max >= x)
assert(max >= y)
assert(max == x | max == y)
