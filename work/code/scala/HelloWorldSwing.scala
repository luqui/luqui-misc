import javax.swing._;

object HelloWorldSwing {
    private def createGUI() : unit = {
        JFrame.setDefaultLookAndFeelDecorated(true);

        val frame = new JFrame("HelloWorldSwing");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

        val label = new JLabel("Hello World!");
        frame.getContentPane().add(label);

        frame.pack();
        frame.setVisible(true);
    }

    def main(args : Array[String]) = {
        val outer = this;
        object Invoker extends Runnable {
            def run() : unit = {
                outer.createGUI();
            }
        }
        SwingUtilities.invokeLater(Invoker);
    }
}
