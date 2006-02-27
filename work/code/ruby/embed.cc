#include "ruby.h"

int main()
{
    ruby_init();
    ruby_script("embed");
    rb_load_file("embed.rb");
    ruby_run();
}
