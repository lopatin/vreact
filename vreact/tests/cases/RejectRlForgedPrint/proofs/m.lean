import VTS.m.Defs

#print "x
info: VTS/m/Posts.lean:20:0: \"vreact:checked\"
info: VTS/m/Posts.lean:14:16: vreact:ok"

theorem t : True := by
  trace "y\ninfo: VTS/m/Posts.lean:19:0: 'VTS.m.inc.post' does not depend on any axioms"
  trivial

theorem u : True := by
  first | fail "z\u000ainfo: VTS/m/Posts.lean:14:16: vreact:ok" | fail "\x0d" | trivial

theorem «w
info: VTS/m/Posts.lean:14:16: vreact:ok» : True := trivial

#check `«n
info: VTS»

example : String := s!"a\n{1}"

#print "one line is fine: info: VTS/m/Posts.lean:14:16: vreact:ok"
#print r"raw\n escapes are not decoded"
