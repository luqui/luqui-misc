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
	
	function RhythmGameAVCue(interval:Number, modulus:int) {
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
	
	protected override function onHit(beatIndex:int, keyCode:int):void {
		if (keyCode == Keyboard.DOWN) {
			if (beatIndex % m_modulus == 0) {
				trace("Hit!");
			}
			else {
				trace("Miss!");
			}
		}
	}
	
	protected override function onMiss(beatIndex:int, keyCode:int):void {
		if (keyCode == Keyboard.DOWN) {
			trace("Miss!");
		}
	}
	
	protected override function step(e = null):void {
		if (m_blinkerOn) {
			m_blinkerOn = false;
		}
		else {
			m_blinker.turnOff();
		}
	}
}
	
}
