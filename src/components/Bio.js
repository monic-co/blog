import React from 'react'

// Import typefaces
// import 'typeface-montserrat'
// import 'typeface-merriweather'

import profilePic from './profile-pic.jpg'

class Bio extends React.Component {
  render() {
    return (
      <div
        style={{
          display: 'flex',
          // marginBottom: rhythm(2.5),
        }}
      >
        <img
          src={profilePic}
          alt={`Joel Burget`}
          style={{
            // marginRight: rhythm(1 / 2),
            marginBottom: 0,
            width: "100px",
            height: "100px",
          }}
        />
        <p>
          <strong>Joel Burget</strong>, cofounder{' '}
        </p>
      </div>
    )
  }
}

export default Bio
