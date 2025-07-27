* [x] print input
* [ ] parse S-exp
  * [x] parse char as Char
  * [x] test RuneStream
  * [x] test Parser
  * [x] test main()
  * [x] parse every seq of non-space characters as Seq
  * [x] parse literal
    * [x] int
    * [x] string
      * [x] "simple" strings without delimiterts or escaping
      * [x] strings with delimiters
      * [x] support simple escaping: `\n \t \" \\`
      * [x] support runes by code: `\uXXXX \UXXXXXXXX`
  * [x] parse symbol
  * [x] parse list
    * [x] empty
    * [x] non-empty
  * [x] quot
    * [x] parse quoted literal
    * [x] parse quoted list
* [ ] evaluate literals
  * [ ] int
  * [ ] string
  * [ ] symbol
* [ ] evaluate special composites
  * [ ] evaluate quoted literal
  * [ ] evaluate quoted symbol
  * [ ] evaluate quoted list
* [ ] substitution model
  * [ ] applicative evaluation order
  * [ ] normal evaluation order
