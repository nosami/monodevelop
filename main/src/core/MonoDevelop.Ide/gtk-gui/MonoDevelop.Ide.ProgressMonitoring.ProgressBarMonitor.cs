
// This file has been generated by the GUI designer. Do not modify.
namespace MonoDevelop.Ide.ProgressMonitoring
{
	public partial class ProgressBarMonitor
	{
		private global::Gtk.HBox hbox1;
		private global::Gtk.ProgressBar progressBar;
		private global::Gtk.Button buttonCancel;

		protected virtual void Build ()
		{
			global::Stetic.Gui.Initialize (this);
			// Widget MonoDevelop.Ide.ProgressMonitoring.ProgressBarMonitor
			global::Stetic.BinContainer.Attach (this);
			this.Name = "MonoDevelop.Ide.ProgressMonitoring.ProgressBarMonitor";
			// Container child MonoDevelop.Ide.ProgressMonitoring.ProgressBarMonitor.Gtk.Container+ContainerChild
			this.hbox1 = new global::Gtk.HBox ();
			this.hbox1.Name = "hbox1";
			this.hbox1.Spacing = 3;
			// Container child hbox1.Gtk.Box+BoxChild
			this.progressBar = new global::Gtk.ProgressBar ();
			this.progressBar.Name = "progressBar";
			this.hbox1.Add (this.progressBar);
			global::Gtk.Box.BoxChild w1 = ((global::Gtk.Box.BoxChild)(this.hbox1 [this.progressBar]));
			w1.Position = 0;
			// Container child hbox1.Gtk.Box+BoxChild
			this.buttonCancel = new global::Gtk.Button ();
			this.buttonCancel.CanFocus = true;
			this.buttonCancel.Name = "buttonCancel";
			this.buttonCancel.UseUnderline = true;
			this.buttonCancel.Relief = ((global::Gtk.ReliefStyle)(2));
			global::Gtk.Image w2 = new global::Gtk.Image ();
			this.buttonCancel.Image = w2;
			this.hbox1.Add (this.buttonCancel);
			global::Gtk.Box.BoxChild w3 = ((global::Gtk.Box.BoxChild)(this.hbox1 [this.buttonCancel]));
			w3.Position = 1;
			w3.Expand = false;
			w3.Fill = false;
			this.Add (this.hbox1);
			if ((this.Child != null)) {
				this.Child.ShowAll ();
			}
			this.Hide ();
		}
	}
}
