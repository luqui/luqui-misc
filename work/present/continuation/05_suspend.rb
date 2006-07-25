def ask(msg)
	print msg
	gets.chomp
end

def three_lines(line, suspend)
	puts "Line One  : #{line}"
	line, suspend = callcc { |cc| suspend.call(cc) }
	puts "Line Two  : #{line}"
	line, suspend = callcc { |cc| suspend.call(cc) }
	puts "Line Three: #{line}"
	callcc { |cc| suspend.call(cc) }
end

resume = callcc { |cc| three_lines(ask("What should line 1 be? "), cc) }
resume = callcc { |cc| resume.call(ask("What should line 2 be? "), cc) }
resume = callcc { |cc| resume.call(ask("What should line 3 be? "), cc) }
