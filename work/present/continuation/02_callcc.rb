ret = callcc do |cc|
	puts "position 1"
	42
end

puts "position 2"
puts ret

ret = callcc do |cc|
	puts "position 3"
	cc.call("boink")
	puts "position 4"
end

puts "position 5"
puts ret
