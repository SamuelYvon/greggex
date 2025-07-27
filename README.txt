# Greg, the small regex engine that could

Some help from
- https://swtch.com/~rsc/regexp/regexp1.html
- https://en.wikipedia.org/wiki/Regular_expression


## Syntax

 <expr> : (<group><modifier>?|<char><modifier>?|<char-group><modifier>?|<any-match><modifier>?)*
 <any-match> : .
 <group> : (<expr>(|<expr>)*)
 <char> : 0-9, a-z, A-Z, !@#$%&*, \<escaped char>
 <char-group> : [ (<range-expr> | <char>)* ]
 <range-expr> : a-a
 <escaped-char>: ,^,$,{,},(,),[,],
 <modifier>: *,+,{l,h},{e}
