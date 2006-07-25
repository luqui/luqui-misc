loopstart, idx = callcc do |cc|
	[cc, 0]
end

puts "Hello #{idx}"

loopstart.call(loopstart, idx+1)
