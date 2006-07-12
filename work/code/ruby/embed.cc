#include "ruby.h"
#include <iostream>

typedef VALUE (*rb_fp)(...);

template <class Ty>
rb_fp rb_fpcast(Ty in) {
	return reinterpret_cast<rb_fp>(in);
}

VALUE add_one(VALUE self, VALUE num)
{
	return INT2NUM(NUM2INT(num) + 1);
}

int main()
{
    ruby_init();
    ruby_script("embed");

	rb_define_global_function("add_one", rb_fpcast(&add_one), 1);
	
    rb_load_file("embed.rb");
    ruby_run();
}
