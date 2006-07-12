def current_continuation
	callcc { |cont| cont.call(cont) }
end

x = 0
cont = current_continuation
	puts "hello" + x.to_s
	x += 1
cont.call(cont)
