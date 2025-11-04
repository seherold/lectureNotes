// #Sireum #Logika
//@Logika: --manual

import org.sireum._

//get user input number, print whether
//it is positive or negative

//what does "val" mean?
  //val means a constant, can't change it's value once set
val num: Z = Z.prompt("Enter a number: ")

if (num > 0) {
  println(num, " is positive")
} else {
  println(num, " is negative (or zero)")
}