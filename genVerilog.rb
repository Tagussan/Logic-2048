class String
  def indent(level = 1, count = 2)
    spaces = ' ' * count * level
    each_line.map {|line| line.chomp.empty? ? line : spaces + line }.join
  end
end

logicFile = open("./logic.txt")
first = true
while line = logicFile.gets
  line =~ /(.+),(.+)/
  condsStr = $1
  assignStr = $2.gsub(/;/, ";\n")
  if first then
    first = false
  else
    print " else "
  end
  puts "if (#{condsStr}) begin"
  puts assignStr.indent(level = 1,count = 4)
  print "end"
end
puts ""
