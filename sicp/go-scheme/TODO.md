* [x] print input
* [ ] parse S-exp
  * [x] parse char as Char
  * [x] test RuneStream
  * [x] test Parser
  * [x] test main()
  * [x] parse every seq of non-space characters as Seq
  * [ ] parse literal
    * [x] int
    * [ ] string
      * [x] "simple" strings without delimiterts or escaping
      * [ ] strings with delimiters
      * [ ] support simple escaping: `\n \t \" \\`
      * [ ] support runes by code: `\uXXX`
  * [x] parse symbol
  * [ ] parse list
  * [ ] quot
    * [ ] parse quoted literal
    * [ ] parse quoted list
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
