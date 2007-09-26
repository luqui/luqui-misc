package {

import flash.utils.Timer;
	
public class Metronome {
	private var m_interval:Number;  // milliseconds
	private var m_timer:Timer;
	private var m_lastFire:Date;
	
	private var m_onFire:Function;
	
	function Metronome(interval:Number) {
		m_interval = interval;
		m_timer = new Timer(m_interval);
	}
	
	public function begin():void {
		m_lastFire = new Date();
		m_timer.start();
		m_timer.addEventListener('timer', onTimer);
	}
	
	public function end():void {
		m_timer.removeEventListener('timer', onTimer);
		m_timer.stop();
	}
	
	public function setFireCallback(cb:Function):void {
		m_onFire = cb;
	}
	
	public function nearestBeat():Object {
		var now = new Date().getTime();
		var lastFire = m_lastFire.getTime();
		if (now - lastFire < m_interval/2) {
			return { index: m_timer.currentCount, offset: now - lastFire };
		}
		else {
			return { index: m_timer.currentCount+1, offset: m_interval - (now - lastFire) };
		}
	}
	
	private function onTimer(e):void {
		m_lastFire = new Date();
		if (m_onFire != null) { m_onFire(m_timer.currentCount); }
	}
}

}