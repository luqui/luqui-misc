loopstart = callcc do |cc|
	cc
end

puts "Hello"

loopstart.call(loopstart)
