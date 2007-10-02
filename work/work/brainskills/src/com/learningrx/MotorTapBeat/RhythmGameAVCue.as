package com.learningrx.MotorTapBeat {
	
import flash.ui.Keyboard;
import flash.media.Sound;
	
public class RhythmGameAVCue extends RhythmGame {
	
	private var m_blinker:Blinker = new Blinker();
	private var m_blinkerOn:Boolean = false;
	private var m_toneOn:Sound = new ToneG4Short();
	private var m_toneOff:Sound = new ToneC4Short();
	private var m_interval:Number;
	private var m_modulus:int;
	private var m_audioCue:Boolean = true;
	
	function RhythmGameAVCue(game:MotorTapBeat, interval:Number, modulus:int) {
		super(game);
		m_interval = interval;
		m_modulus = modulus;
		addChild(m_blinker);
	}
	
	public function setVisualCue(stat:Boolean):void {
		m_blinker.visible = stat;
	}
	
	public function setAudioCue(stat:Boolean):void {
		m_audioCue = stat;
	}
	
	protected override function makeMetronome():Metronome {
		var met = new Metronome(m_interval);
		var self = this;
		met.setFireCallback(function(count) {
			if (count % m_modulus == 0) {
				if (m_audioCue) { m_toneOn.play(); }
				m_blinker.turnGreen();
			}
			else {
				if (m_audioCue) { m_toneOff.play(); }
				m_blinker.turnRed();
			}
			self.m_blinkerOn = true;
		});
		return met;
	}
	
	protected override function beatCounts(beatIndex:int):Boolean {
		return beatIndex % m_modulus == 0;
	}
	
	protected override function onHit(beatIndex:int, dir:String):void {
		m_game.ScoreRight();
	}
	
	protected override function onMissHit(beatIndex:int, dir:String):void {
		m_game.ScoreWrong();
	}
	
	protected override function onMiss(beatIndex:int):void {
		m_game.ScoreWrong();
	}
	
	protected override function step(e = null):void {
		super.step(e);
		if (m_blinkerOn) {
			m_blinkerOn = false;
		}
		else {
			m_blinker.turnOff();
		}
	}
}
	
}
