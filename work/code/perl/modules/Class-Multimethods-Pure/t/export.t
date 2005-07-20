package NumberOne;

use Test::More tests => 10;

use Class::Multimethods::Pure;

ok(exists(&multi), "multi default");
ok(exists(&All),   "All default");
ok(exists(&Any),   "Any default");
ok(exists(&None),  "None default");

package NumberTwo;

use Test::More;

use Class::Multimethods::Pure import => qw<multi None>;

ok(exists(&multi), "multi explicit");
ok(!exists(&All),  "All explicit");
ok(!exists(&Any),  "Any explicit");
ok(exists(&None),  "None explicit");

package NumberThree;

use Test::More;

use Class::Multimethods::Pure multi => 
        foo => qw<ARRAY> => sub { "Calloh Callay" };

ok(!exists(&multi), "no exports on use-time multi");
is(foo([]), "Calloh Callay", "Actually defines the multi");
